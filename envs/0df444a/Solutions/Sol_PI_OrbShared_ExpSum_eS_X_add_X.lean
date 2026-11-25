-- Prove2me | solution 1 for PI.OrbShared.ExpSum.eS_X_add_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:47.69472+00:00
-- url     : https://prove2.me/submissions/567ece8a-ba3f-431e-8f84-654b7b5da337

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
import Theorems.Thm_PI_OrbShared_ExpSum_fin_two_vector_eq_matrixVecCons
import Theorems.Thm_PI_OrbShared_ExpSum_coeff_X_add_X_pow
import Theorems.Thm_PI_OrbShared_ExpSum_coeff_exp_K
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
private lemma coeff_eS_X (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    coeff e (eS (X i : MvPowerSeries (Fin 2) K)) =
      if e = Finsupp.single i (e i) then ((e i).factorial : K)⁻¹ else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp only [coeff_X_pow, coeff_exp_K, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h]
    · intro d hd
      rw [if_neg]
      intro h'
      apply hd
      rw [h']
      simp
  · apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp
variable {τ υ : Type*}
end PI.OrbShared.ExpSum
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
namespace PI.OrbShared.ExpSum
theorem _root_.solution : eS (X 0 + X 1 : MvPowerSeries (Fin 2) K) = eS (X 0) * eS (X 1) := by
  ext e
  have hL : coeff e (eS (X 0 + X 1 : MvPowerSeries (Fin 2) K)) =
      ((e 0 + e 1).factorial : K)⁻¹ * ((e 0 + e 1).choose (e 0) : K) := by
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
    rw [finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_exp_K, coeff_X_add_X_pow, if_pos rfl, smul_eq_mul]
    · intro d hd
      rw [coeff_X_add_X_pow, if_neg (fun h => hd h.symm), smul_zero]
  rw [hL, MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
  · rw [coeff_eS_X, coeff_eS_X, if_pos (by simp), if_pos (by simp)]
    simp only [Finsupp.single_eq_same]
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (e 0) (e 1))
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : ((e 0 + e 1).choose (e 0) : K) * (e 0).factorial * (e 1).factorial =
        (e 0 + e 1).factorial := by exact_mod_cast h1
    have f0 : ((e 0).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have f1 : ((e 1).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hC : ((e 0 + e 1).choose (e 0) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    rw [← h2]
    field_simp
  · rintro ⟨p1, p2⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [coeff_eS_X, coeff_eS_X]
    by_cases h1 : p1 = Finsupp.single 0 (p1 0)
    · by_cases h2 : p2 = Finsupp.single 1 (p2 1)
      · exfalso
        apply hne
        have e0 : e 0 = p1 0 := by
          rw [← hp, Finsupp.add_apply, h2]
          simp
        have e1 : e 1 = p2 1 := by
          rw [← hp, Finsupp.add_apply, h1]
          simp
        rw [h1, h2, e0, e1]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr ((fin_two_vector_eq_matrixVecCons e (e 0) (e 1)).mpr ⟨rfl, rfl⟩).symm) h
end PI.OrbShared.ExpSum
