/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!
# fderiv currying lemmas

Various lemmas related to fderiv on curried/uncurried functions.

-/

@[expose] public section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma fderiv_uncurry (f : X → Y → Z) (xy dxy : X × Y)
    (hf : DifferentiableAt 𝕜 (↿f) xy) :
    fderiv 𝕜 ↿f xy dxy
    =
    fderiv 𝕜 (f · xy.2) xy.1 dxy.1 + fderiv 𝕜 (f xy.1 ·) xy.2 dxy.2 := by
  have hx : (f · xy.2) = ↿f ∘ (fun x' => (x',xy.2)) := by rfl
  have hy : (f xy.1 ·) = ↿f ∘ (fun y' => (xy.1,y')) := by rfl
  rw [hx,hy]
  repeat rw [fderiv_comp (hg := by fun_prop) (hf := by fun_prop)]
  dsimp
  rw [← ContinuousLinearMap.map_add]
  congr
  repeat rw [DifferentiableAt.fderiv_prodMk (hf₁ := by fun_prop) (hf₂ := by fun_prop)]
  simp

lemma fderiv_curry_fst (f : X × Y → Z) (x : X) (y : Y)
    (h : DifferentiableAt 𝕜 f (x,y)) (dx : X) :
    fderiv 𝕜 (fun x' => Function.curry f x' y) x dx = fderiv 𝕜 f (x,y) (dx, 0) := by
  have h1 : f = ↿(Function.curry f) := by
    ext x
    rfl
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry]
  simp only [Function.curry_apply, map_zero, add_zero]
  exact h

lemma fderiv_curry_snd (f : X × Y → Z) (x : X) (y : Y)
    (h : DifferentiableAt 𝕜 f (x,y)) (dy : Y) :
    fderiv 𝕜 (Function.curry f x) y dy = fderiv 𝕜 (f) (x,y) (0, dy) := by
  have h1 : f = ↿(Function.curry f) := by
    ext x
    rfl
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry]
  simp
  rfl
  exact h

lemma fderiv_uncurry_clm_comp (f : X → Y → Z) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 ↿f
    =
    fun xy =>
      (fderiv 𝕜 (f · xy.2) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
      +
      (fderiv 𝕜 (f xy.1 ·) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) := by
  funext xy
  apply ContinuousLinearMap.ext
  intro dxy
  rw [fderiv_uncurry]
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_fst', Function.comp_apply, ContinuousLinearMap.coe_snd']
  fun_prop

lemma fderiv_wrt_prod {f : X × Y → Z} {xy} (hf : DifferentiableAt 𝕜 f xy) :
    fderiv 𝕜 f xy
    =
    (fderiv 𝕜 (fun x' => f (x',xy.2)) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
    +
    (fderiv 𝕜 (fun y' => f (xy.1,y')) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) := by
  apply ContinuousLinearMap.ext; intro (dx,dy)
  apply fderiv_uncurry (fun x y => f (x,y)) _ _ hf

lemma fderiv_wrt_prod_clm_comp (f : X × Y → Z) (hf : Differentiable 𝕜 f) :
    fderiv 𝕜 f
    =
    fun xy =>
      (fderiv 𝕜 (fun x' => f (x',xy.2)) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
      +
      (fderiv 𝕜 (fun y' => f (xy.1,y')) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) :=
  fderiv_uncurry_clm_comp (fun x y => f (x,y)) hf

lemma fderiv_curry_clm_apply (f : X → Y →L[𝕜] Z) (y : Y) (x dx : X) (h : Differentiable 𝕜 f) :
    fderiv 𝕜 f x dx y
    =
    fderiv 𝕜 (f · y) x dx := by
  rw [fderiv_clm_apply] <;> first | simp | fun_prop

/- Helper rw lemmas for proving differentiability conditions. -/
lemma fderiv_uncurry_comp_fst (f : X → Y → Z) (y : Y) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 (fun x' => (↿f) (x', y))
    =
    fun x => (fderiv 𝕜 (↿f) ((·, y) x)).comp (fderiv 𝕜 (·, y) x) := by
  have hl (y : Y) : (fun x' => (↿f) (x', y)) = ↿f ∘ (·, y) := by
    rfl
  rw [hl]
  funext x
  rw [fderiv_comp]
  · fun_prop
  · fun_prop

lemma fderiv_uncurry_comp_snd (f : X → Y → Z) (x : X) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 (fun y' => (↿f) (x, y'))
    =
    fun y => (fderiv 𝕜 (↿f) ((x, ·) y)).comp (fderiv 𝕜 (x, ·) y) := by
  have hl (x : X) : (fun y' => (↿f) (x, y')) = ↿f ∘ (x, ·) := by
    rfl
  rw [hl]
  funext y
  rw [fderiv_comp]
  · fun_prop
  · fun_prop

lemma fderiv_curry_comp_fst (f : X → Y → Z) (x dx : X) (y : Y)
    (hf : Differentiable 𝕜 (↿f)) :
    (fderiv 𝕜 (fun x' => f x' y) x) dx
    =
    (fderiv 𝕜 (↿f) ((·, y) x)) ((fderiv 𝕜 (·, y) x) dx) := by
  have hl (y : Y) : (fun x' => f x' y) = ↿f ∘ (·, y) := by
    rfl
  rw [hl]
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  · fun_prop
  · fun_prop

lemma fderiv_curry_comp_snd (f : X → Y → Z) (x : X) (y dy : Y)
    (hf : Differentiable 𝕜 (↿f)) :
    (fderiv 𝕜 (fun y' => f x y') y) dy
    =
    (fderiv 𝕜 (↿f) ((x, ·) y)) ((fderiv 𝕜 (x, ·) y) dy) := by
  have hl (x : X) : (fun y' => f x y') = ↿f ∘ (x, ·) := by
    rfl
  rw [hl]
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  · fun_prop
  · fun_prop

lemma fderiv_inr_fst_clm (x : X) (y : Y) :
    (fderiv 𝕜 (x, ·) y) = ContinuousLinearMap.inr 𝕜 X Y := by
  rw [(hasFDerivAt_prodMk_right x y).fderiv]

lemma fderiv_inl_snd_clm (x : X) (y : Y) :
    (fderiv 𝕜 (·, y) x) = ContinuousLinearMap.inl 𝕜 X Y := by
  rw [(hasFDerivAt_prodMk_left x y).fderiv]

/- Differentiability conditions. -/

lemma function_differentiableAt_fst (f : X → Y → Z) (x : X) (y : Y) (hf : Differentiable 𝕜 (↿f)) :
    DifferentiableAt 𝕜 (fun x' => f x' y) x := by
  have hl : (fun x' => f x' y) = ↿f ∘ (·, y) := by
    funext x'
    rfl
  rw [hl]
  apply Differentiable.differentiableAt
  apply Differentiable.comp <;> fun_prop

lemma function_differentiableAt_snd (f : X → Y → Z) (x : X) (y : Y) (hf : Differentiable 𝕜 (↿f)) :
    DifferentiableAt 𝕜 (fun y' => f x y') y := by
  have hl : (fun y' => f x y') = ↿f ∘ (x, ·) := by
    funext y'
    rfl
  rw [hl]
  apply Differentiable.differentiableAt
  apply Differentiable.comp <;> fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_fst (f : X → Y → Z) (y : Y) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fderiv 𝕜 fun x' => (↿f) (x', y)) := by
  fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_snd (f : X → Y → Z) (x : X) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fderiv 𝕜 fun y' => (↿f) (x, y')) := by
  fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_fst_comp_snd (f : X → Y → Z) (x : X) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun y' => fderiv 𝕜 (fun x' => (↿f) (x', y')) x) := by
  fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_fst_comp_snd_apply (f : X → Y → Z) (x δx : X)
    (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun y' => fderiv 𝕜 (fun x' => (↿f) (x', y')) x δx) := by
  fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_snd_comp_fst (f : X → Y → Z) (y : Y) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun x' => fderiv 𝕜 (fun y' => (↿f) (x', y')) y) := by
  fun_prop

@[fun_prop]
lemma fderiv_uncurry_differentiable_snd_comp_fst_apply (f : X → Y → Z) (y δy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun x' => fderiv 𝕜 (fun y' => (↿f) (x', y')) y δy) := by
  fun_prop

@[fun_prop]
lemma fderiv_curry_differentiableAt_fst_comp_snd (f : X → Y → Z) (x dx : X) (y : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    DifferentiableAt 𝕜 (fun y' => (fderiv 𝕜 (fun x' => f x' y') x) dx) y := by
  apply Differentiable.differentiableAt
  fun_prop

lemma fderiv_curry_differentiableAt_snd_comp_fst (f : X → Y → Z) (x : X) (y dy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    DifferentiableAt 𝕜 (fun x' => (fderiv 𝕜 (fun y' => f x' y') y) dy) x := by
  apply Differentiable.differentiableAt
  fun_prop

/-- Mixed partial derivatives of `f x y` commute at a point near which `↿f` is twice
continuously differentiable. A local version of `fderiv_swap`. -/
lemma fderiv_swap_of_contDiffAt [IsRCLikeNormedField 𝕜] (f : X → Y → Z) (x dx : X) (y dy : Y)
    (hf : ContDiffAt 𝕜 2 ↿f (x, y)) :
    fderiv 𝕜 (fun x' ↦ fderiv 𝕜 (fun y' ↦ f x' y') y dy) x dx =
      fderiv 𝕜 (fun y' ↦ fderiv 𝕜 (fun x' ↦ f x' y') x dx) y dy := by
  have hd : ∀ᶠ p in nhds (x, y), DifferentiableAt 𝕜 ↿f p :=
    (hf.eventually (by simp)).mono fun p hp ↦ hp.differentiableAt (by simp)
  have hD : HasFDerivAt (fderiv 𝕜 ↿f) (fderiv 𝕜 (fderiv 𝕜 ↿f) (x, y)) (x, y) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have h1 : (fun x' ↦ fderiv 𝕜 (fun y' ↦ f x' y') y dy) =ᶠ[nhds x]
      fun x' ↦ fderiv 𝕜 ↿f (x', y) (0, dy) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hd]
      with x' hx'
    simp [fderiv_uncurry f (x', y) (0, dy) hx']
  have h2 : (fun y' ↦ fderiv 𝕜 (fun x' ↦ f x' y') x dx) =ᶠ[nhds y]
      fun y' ↦ fderiv 𝕜 ↿f (x, y') (dx, 0) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.eventually hd]
      with y' hy'
    simp [fderiv_uncurry f (x, y') (dx, 0) hy']
  have hx : HasFDerivAt (fun x' ↦ fderiv 𝕜 ↿f (x', y) (0, dy)) _ x :=
    (hD.comp x (hasFDerivAt_prodMk_left x y)).clm_apply (hasFDerivAt_const _ x)
  have hy : HasFDerivAt (fun y' ↦ fderiv 𝕜 ↿f (x, y') (dx, 0)) _ y :=
    (hD.comp y (hasFDerivAt_prodMk_right x y)).clm_apply (hasFDerivAt_const _ y)
  rw [h1.fderiv_eq, h2.fderiv_eq, hx.fderiv, hy.fderiv]
  simpa using (hf.isSymmSndFDerivAt (by simp)).eq (dx, 0) (0, dy)

/-- Mixed partial derivatives of `f x y` commute when `↿f` is twice continuously
differentiable. -/
lemma fderiv_swap [IsRCLikeNormedField 𝕜] (f : X → Y → Z) (x dx : X) (y dy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    fderiv 𝕜 (fun x' ↦ fderiv 𝕜 (fun y' ↦ f x' y') y dy) x dx =
      fderiv 𝕜 (fun y' ↦ fderiv 𝕜 (fun x' ↦ f x' y') x dx) y dy :=
  fderiv_swap_of_contDiffAt f x dx y dy hf.contDiffAt
