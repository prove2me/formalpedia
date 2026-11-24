-- Prove2me | solution 1 for RoughSurfaceScattering.harmonic_iteratedFDeriv_R3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T06:22:05.955077+00:00
-- url     : https://prove2.me/submissions/57d50dfb-7a5f-45e4-8d4b-c967c16d38fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_harmonic_smooth_R3

open MeasureTheory InnerProductSpace Laplacian
open RoughSurfaceScattering

abbrev R3 := EuclideanSpace ℝ (Fin 3)

lemma symm_of_C2 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : R3 → G) (z : R3)
    (hg : ContDiffAt ℝ 2 g z) : IsSymmSndFDerivAt ℝ g z :=
  hg.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])

/-- `D(w ↦ D²g(w)[a,b])(z)[v] = D³g(z)[v,a,b]`. -/
lemma fderiv_d2_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : R3 → G)
    (z a b v : R3) (hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ g)) z) :
    fderiv ℝ (fun w => fderiv ℝ (fderiv ℝ g) w a b) z v =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) z v a b := by
  have h1 : DifferentiableAt ℝ (fun w => fderiv ℝ (fderiv ℝ g) w a) z :=
    hd.clm_apply (differentiableAt_const a)
  rw [fderiv_clm_apply h1 (differentiableAt_const b), fderiv_clm_apply hd (differentiableAt_const a)]
  simp

/-- The Laplacian commutes with `fderiv` for `C³` functions. -/
lemma laplacian_fderiv_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : R3 → G)
    (z v : R3) (hg : ContDiffAt ℝ 3 g z) :
    Δ (fderiv ℝ g) z v = fderiv ℝ (Δ g) z v := by
  set b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hg2 : ∀ᶠ w in nhds z, ContDiffAt ℝ 2 g w :=
    (hg.eventually (by simp)).mono fun w hw => hw.of_le (by norm_num)
  have hDg : ContDiffAt ℝ 2 (fderiv ℝ g) z := hg.fderiv_right (by norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ g)) z :=
    (hg.fderiv_right (m := 2) (by norm_num) |>.fderiv_right (m := 1) (by norm_num)
      |>.differentiableAt one_ne_zero)
  -- left side
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (fderiv ℝ g) b]
  simp only [ContinuousLinearMap.sum_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- right side
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis g b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hdiff : ∀ i, DifferentiableAt ℝ (fun w => fderiv ℝ (fderiv ℝ g) w (b i) (b i)) z :=
    fun i => (hdd.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  rw [fderiv_fun_sum fun i _ => hdiff i, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_d2_apply g z (b i) (b i) v hdd]
  -- `D³g(z)[e,e,v] = D³g(z)[e,v,e] = D³g(z)[v,e,e]`
  have hS1 := symm_of_C2 (fderiv ℝ g) z hDg
  have hev : (fun w => fderiv ℝ (fderiv ℝ g) w (b i) v) =ᶠ[nhds z]
      (fun w => fderiv ℝ (fderiv ℝ g) w v (b i)) :=
    hg2.mono fun w hw => symm_of_C2 g w hw (b i) v
  have h2 : fderiv ℝ (fderiv ℝ (fderiv ℝ g)) z (b i) (b i) v =
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) z (b i) v (b i) := by
    rw [← fderiv_d2_apply g z (b i) v (b i) hdd, ← fderiv_d2_apply g z v (b i) (b i) hdd,
      hev.fderiv_eq]
  rw [h2, hS1 (b i) v]

/-- Derivatives of smooth harmonic functions are harmonic. -/
lemma harmonic_fderiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : R3 → G)
    (U : Set R3) (hU : IsOpen U) (hsm : ∀ m : ℕ, ContDiffOn ℝ m g U)
    (hh : HarmonicOnNhd g U) : HarmonicOnNhd (fderiv ℝ g) U := by
  intro w hw
  have h3 : ∀ y ∈ U, ContDiffAt ℝ 3 g y := fun y hy => (hsm 3).contDiffAt (hU.mem_nhds hy)
  refine ⟨(h3 w hw).fderiv_right (by norm_num), ?_⟩
  filter_upwards [hU.mem_nhds hw] with y hy
  ext v
  rw [laplacian_fderiv_apply g y v (h3 y hy), (hh y hy).2.fderiv_eq]
  simp

theorem solution (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) :
    ∀ n : ℕ, InnerProductSpace.HarmonicOnNhd (iteratedFDeriv ℝ n f) U := by
  have hsmf := harmonic_smooth_R3 f U hU hf
  have key : ∀ n : ℕ, HarmonicOnNhd (iteratedFDeriv ℝ n f) U ∧
      ∀ m : ℕ, ContDiffOn ℝ m (iteratedFDeriv ℝ n f) U := by
    intro n
    induction n with
    | zero =>
      rw [iteratedFDeriv_zero_eq_comp]
      set L := (continuousMultilinearCurryFin0 ℝ R3 ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
      exact ⟨hf.comp_CLM L, fun m => (hsmf m).continuousLinearMap_comp L⟩
    | succ n ih =>
      rw [iteratedFDeriv_succ_eq_comp_left]
      set L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => R3) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
      have hsmD : ∀ m : ℕ, ContDiffOn ℝ m (fderiv ℝ (iteratedFDeriv ℝ n f)) U := fun m =>
        (ih.2 (m + 1)).fderiv_of_isOpen hU (by push_cast; exact le_rfl)
      exact ⟨(harmonic_fderiv _ U hU ih.2 ih.1).comp_CLM L,
        fun m => (hsmD m).continuousLinearMap_comp L⟩
  exact fun n => (key n).1
