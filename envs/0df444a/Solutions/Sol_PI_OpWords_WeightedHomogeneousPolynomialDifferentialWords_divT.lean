-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.divT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:21.630895+00:00
-- url     : https://prove2.me/submissions/5d839995-d784-4b88-a6f5-9f74c70e744b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_homog_of_mul
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_isWeightedHomogeneous_pairing_left
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_tt_homog_xi
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_tt_ne_zero
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_not_X_dvd_tt
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_dvd_of_dvd_X_pow
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_dvd_pow_mul
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_divT_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
theorem _root_.solution : PI.OpWords.DivT := by
  intro K _ _ k d hd f hf hv
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  have hfx : IsWeightedHomogeneous (wx k) f d := by
    have h1 := (Submodule.mem_inf.1 hf').1
    rwa [mem_weightedHomogeneousSubmodule] at h1
  have hfxi : IsWeightedHomogeneous (wxi k) f d := by
    have h2 := (Submodule.mem_inf.1 hf').2
    rwa [mem_weightedHomogeneousSubmodule] at h2
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [mul_zero]
    ext m
    rw [coeff_zero]
    by_contra h
    have h1 := hfx h
    have h2 : m = 0 := by
      ext v
      rcases v with i | i <;> exact i.elim0
    rw [h2, map_zero] at h1
    omega
  · have hdvd : tt K k ∣ f := by
      rcases Nat.lt_or_ge k 2 with hk | hk
      · obtain rfl : k = 1 := by omega
        exact divT_one d hd f hf
      · exact dvd_of_dvd_X_pow (not_X_dvd_tt (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩
          (by simp [Fin.ext_iff])) d (dvd_pow_mul _ d f hf hv)
    obtain ⟨g, rfl⟩ := hdvd
    have e : 1 + (d - 1) = d := by omega
    refine ⟨g, Submodule.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
    · rw [mem_weightedHomogeneousSubmodule]
      exact homog_of_mul (wx k) isWeightedHomogeneous_pairing_left (tt_ne_zero hk1) (by rw [e]; exact hfx)
    · rw [mem_weightedHomogeneousSubmodule]
      exact homog_of_mul (wxi k) tt_homog_xi (tt_ne_zero hk1) (by rw [e]; exact hfxi)
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
