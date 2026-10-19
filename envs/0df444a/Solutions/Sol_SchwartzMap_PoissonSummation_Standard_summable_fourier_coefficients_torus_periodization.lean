-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.summable_fourier_coefficients_torus_periodization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/804a594a-d512-4a25-9fc9-895931e23d88

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_fourier_coefficient_torus_periodization

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform
open MeasureTheory
open SchwartzMap SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution :
    Summable (UnitAddTorus.mFourierCoeff (torusDescendedPeriodization (d := d) f)) := by
  have hsum_norm :
      Summable (fun n : Fin d → ℤ =>
        ‖𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)‖) := by
    let k : ℕ := d + 1
    have hk : Module.finrank ℤ (SchwartzMap.referenceIntegerLattice d) < k := by
      have hrank : Module.finrank ℤ (SchwartzMap.referenceIntegerLattice d) = d := by
        have h := (ZLattice.rank (K := ℝ) (L := (SchwartzMap.referenceIntegerLattice d)))
        simpa using! (h.trans (by simp))
      simp [hrank, k]
    obtain ⟨C, hCpos, hC⟩ := (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) f).decay k 0
    have hC' : ∀ x : (EuclideanSpace ℝ (Fin d)), ‖x‖ ^ k * ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) x‖ ≤ C := by
      simpa [FourierTransform.fourierCLE_apply, fourier_coe, norm_iteratedFDeriv_zero] using! hC
    have hsum_pow :
        Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k : ℝ)) := by
      simpa [k] using! (ZLattice.summable_norm_pow_inv (L := (SchwartzMap.referenceIntegerLattice d)) (n := k) hk)
    have hsum_bd : Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => (C : ℝ) * (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k)) :=
      hsum_pow.mul_left C
    have hsum_lattice : Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) (ℓ : (EuclideanSpace ℝ (Fin d)))‖) := by
      have hfin : ({ℓ : (SchwartzMap.referenceIntegerLattice d) | ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ (1 : ℝ)} : Set _).Finite :=
        finite_reference_lattice_points_of_norm_bound (d := d) 1
      refine Summable.of_norm_bounded_eventually hsum_bd ?_
      filter_upwards [hfin.compl_mem_cofinite] with ℓ hℓ
      have hnorm_gt : (1 : ℝ) < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_of_not_ge (by simpa using! hℓ)
      have hnorm_pos : 0 < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_trans (by positivity) hnorm_gt
      have hpow_pos : 0 < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ^ k := pow_pos hnorm_pos _
      have hmain := hC' (ℓ : (EuclideanSpace ℝ (Fin d)))
      have : ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) (ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ C / (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ^ k) :=
        (le_div_iff₀' hpow_pos).2 hmain
      have hdiv :
          ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) (ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ (C : ℝ) * (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) := by
        simpa [div_eq_mul_inv, inv_pow, one_div] using! this
      simpa [Real.norm_of_nonneg (norm_nonneg _)] using! hdiv
    let e := (PoissonSummation.Standard.integerVectorLatticeEquiv (d := d))
    have : Summable (fun n : Fin d → ℤ => ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) ((e n : (SchwartzMap.referenceIntegerLattice d)) : (EuclideanSpace ℝ (Fin d)))‖) := by
      simpa using! (Summable.comp_injective hsum_lattice e.injective)
    simpa [PoissonSummation.Standard.integerVectorLatticeEquiv] using! this
  refine (Summable.of_norm ?_)
  simpa [fourier_coefficient_torus_periodization (d := d) (f := f)] using! hsum_norm
end SchwartzMap.PoissonSummation.Standard
