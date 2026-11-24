-- Prove2me | solution 1 for RoughSurfaceScattering.helmholtz_descent_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:55:30.193035+00:00
-- url     : https://prove2.me/submissions/d9ef194a-fab8-4a22-a9f3-b02476573546

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory InnerProductSpace
open RoughSurfaceScattering

abbrev R3 := EuclideanSpace ℝ (Fin 3)

noncomputable def projP : R3 →L[ℝ] R2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => pt (y 0) (y 1)
      map_add' := fun x y => by ext i; fin_cases i <;> simp [pt]
      map_smul' := fun c x => by ext i; fin_cases i <;> simp [pt] }

noncomputable def projQ : R3 →L[ℝ] ℝ := EuclideanSpace.proj 2

lemma projP_apply (y : R3) : projP y = pt (y 0) (y 1) := rfl
lemma projQ_apply (y : R3) : projQ y = y 2 := rfl

/-- `∂_e (fderiv f · d)` written through the second derivative. -/
lemma iter2_eq (f : R2 → ℂ) (x e : R2) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    iteratedFDeriv ℝ 2 f x ![e, e] = fderiv ℝ (fun y => fderiv ℝ f y e) x e := by
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hf (differentiableAt_const e)]
  simp

lemma iter2_eq3 (f : R3 → ℂ) (x e : R3) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    iteratedFDeriv ℝ 2 f x ![e, e] = fderiv ℝ (fun y => fderiv ℝ f y e) x e := by
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hf (differentiableAt_const e)]
  simp

/-- First derivative of `v = (u ∘ P) · e^{k q}`. -/
lemma fderiv_v_apply (k : ℝ) (u : R2 → ℂ) (w e : R3) (hu : DifferentiableAt ℝ u (projP w)) :
    fderiv ℝ (fun y => u (projP y) * ((Real.exp (k * projQ y) : ℝ) : ℂ)) w e =
      u (projP w) * ((k * Real.exp (k * projQ w) * projQ e : ℝ) : ℂ) +
        ((Real.exp (k * projQ w) : ℝ) : ℂ) * fderiv ℝ u (projP w) (projP e) := by
  have ha : HasFDerivAt (fun y => u (projP y)) ((fderiv ℝ u (projP w)).comp projP) w :=
    hu.hasFDerivAt.comp w projP.hasFDerivAt
  have hr : HasFDerivAt (fun y => Real.exp (k * projQ y))
      (Real.exp (k * projQ w) • (k • projQ)) w :=
    (projQ.hasFDerivAt.const_mul k).exp
  have hb := Complex.ofRealCLM.hasFDerivAt.comp w hr
  have hv : HasFDerivAt (fun y => u (projP y) * ((Real.exp (k * projQ y) : ℝ) : ℂ)) _ w :=
    ha.mul hb
  rw [hv.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

lemma contDiffAt_v (k : ℝ) (u : R2 → ℂ) (z : R3) (hu : ContDiffAt ℝ 2 u (projP z)) :
    ContDiffAt ℝ 2 (fun y => u (projP y) * ((Real.exp (k * projQ y) : ℝ) : ℂ)) z := by
  have h1 : ContDiffAt ℝ 2 (fun y => u (projP y)) z := hu.comp z projP.contDiff.contDiffAt
  have h2 : ContDiff ℝ 2 (fun y : R3 => ((Real.exp (k * projQ y) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp
      ((contDiff_const (c := k)).mul projQ.contDiff))
  exact h1.mul h2.contDiffAt

/-- Second directional derivative of `v = (u ∘ P) · e^{k q}`. -/
lemma second_dir (k : ℝ) (G : Set R2) (hG : IsOpen G) (u : R2 → ℂ)
    (hu : ContDiffOn ℝ 2 u G) (z : R3) (hz : projP z ∈ G) (e : R3) :
    iteratedFDeriv ℝ 2 (fun y => u (projP y) * ((Real.exp (k * projQ y) : ℝ) : ℂ)) z ![e, e] =
      u (projP z) * ((k ^ 2 * Real.exp (k * projQ z) * projQ e ^ 2 : ℝ) : ℂ) +
        2 * ((k * Real.exp (k * projQ z) * projQ e : ℝ) : ℂ) * fderiv ℝ u (projP z) (projP e) +
        ((Real.exp (k * projQ z) : ℝ) : ℂ) *
          fderiv ℝ (fun x => fderiv ℝ u x (projP e)) (projP z) (projP e) := by
  set v := fun y => u (projP y) * ((Real.exp (k * projQ y) : ℝ) : ℂ) with hv
  have hS : IsOpen {y : R3 | projP y ∈ G} := hG.preimage projP.continuous
  have huA : ∀ x ∈ G, ContDiffAt ℝ 2 u x := fun x hx => hu.contDiffAt (hG.mem_nhds hx)
  have hvz : ContDiffAt ℝ 2 v z := contDiffAt_v k u z (huA _ hz)
  have hdv : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hvz.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [iter2_eq3 v z e hdv]
  -- `fderiv v · e` near `z`
  set g : R3 → ℂ := fun w => u (projP w) * ((k * Real.exp (k * projQ w) * projQ e : ℝ) : ℂ) +
      ((Real.exp (k * projQ w) : ℝ) : ℂ) * fderiv ℝ u (projP w) (projP e) with hg
  have hev : (fun w => fderiv ℝ v w e) =ᶠ[nhds z] g :=
    Filter.eventually_of_mem (hS.mem_nhds hz) fun w hw =>
      fderiv_v_apply k u w e ((huA _ hw).differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  -- derivative of `g`
  have hduz : DifferentiableAt ℝ u (projP z) := (huA _ hz).differentiableAt (by norm_num)
  have hddu : DifferentiableAt ℝ (fderiv ℝ u) (projP z) :=
    ((huA _ hz).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA : HasFDerivAt (fun w => u (projP w)) ((fderiv ℝ u (projP z)).comp projP) z :=
    hduz.hasFDerivAt.comp z projP.hasFDerivAt
  have hr : HasFDerivAt (fun w => Real.exp (k * projQ w))
      (Real.exp (k * projQ z) • (k • projQ)) z :=
    (projQ.hasFDerivAt.const_mul k).exp
  have hB := Complex.ofRealCLM.hasFDerivAt.comp z hr
  have hC := Complex.ofRealCLM.hasFDerivAt.comp z ((hr.const_mul k).mul_const (projQ e))
  have hH : HasFDerivAt (fun w => fderiv ℝ u (projP w) (projP e))
      ((fderiv ℝ (fun x => fderiv ℝ u x (projP e)) (projP z)).comp projP) z :=
    (hddu.clm_apply (differentiableAt_const _)).hasFDerivAt.comp z projP.hasFDerivAt
  have htot : HasFDerivAt g _ z := (hA.mul hC).add (hB.mul hH)
  rw [htot.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    Function.comp_apply]
  push_cast
  ring

lemma pt10 : pt 1 0 = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
  ext i; fin_cases i <;> simp [pt]

lemma pt01 : pt 0 1 = EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  ext i; fin_cases i <;> simp [pt]

lemma pt00 : pt 0 0 = (0 : R2) := by
  ext i; fin_cases i <;> simp [pt]

theorem solution (k : ℝ) (G : Set R2) (hG : IsOpen G) (u : R2 → ℂ)
    (hu : ContDiffOn ℝ 2 u G) (hH : IsHelmholtzOn G k u) :
    InnerProductSpace.HarmonicOnNhd
      (fun y : EuclideanSpace ℝ (Fin 3) => u (pt (y 0) (y 1)) * (Real.exp (k * y 2) : ℂ))
      {y : EuclideanSpace ℝ (Fin 3) | pt (y 0) (y 1) ∈ G} := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin 3) => u (pt (y 0) (y 1)) * (Real.exp (k * y 2) : ℂ))
      = fun y => u (projP y) * ((Real.exp (k * projQ y) : ℝ) : ℂ) := rfl
  have hset : {y : EuclideanSpace ℝ (Fin 3) | pt (y 0) (y 1) ∈ G} = {y | projP y ∈ G} := rfl
  rw [hfun, hset]
  have hS : IsOpen {y : R3 | projP y ∈ G} := hG.preimage projP.continuous
  have huA : ∀ x ∈ G, ContDiffAt ℝ 2 u x := fun x hx => hu.contDiffAt (hG.mem_nhds hx)
  intro z hz
  refine ⟨contDiffAt_v k u z (huA _ hz), ?_⟩
  filter_upwards [hS.mem_nhds hz] with w hw
  have hw' : projP w ∈ G := hw
  -- the 2D Helmholtz equation at `P w`, in coordinates
  have hddu : DifferentiableAt ℝ (fderiv ℝ u) (projP w) :=
    ((huA _ hw').fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hHw := hH (projP w) hw'
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin 2) ℝ)] at hHw
  simp only [Fin.sum_univ_two, EuclideanSpace.basisFun_apply] at hHw
  rw [iter2_eq u _ _ hddu, iter2_eq u _ _ hddu, ← pt10, ← pt01] at hHw
  -- the 3D Laplacian of `v`
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [Fin.sum_univ_three, EuclideanSpace.basisFun_apply]
  rw [second_dir k G hG u hu w hw', second_dir k G hG u hu w hw', second_dir k G hG u hu w hw']
  simp only [projQ_apply, projP_apply, EuclideanSpace.single_apply]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, pt00, map_zero, ContinuousLinearMap.zero_apply]
  simp only [projP_apply] at hHw
  simp only [Pi.zero_apply]
  push_cast
  linear_combination Complex.exp ((k : ℂ) * ((w 2 : ℝ) : ℂ)) * hHw
