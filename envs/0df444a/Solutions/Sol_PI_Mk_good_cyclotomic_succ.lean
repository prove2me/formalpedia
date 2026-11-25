-- Prove2me | solution 1 for PI.Mk.good_cyclotomic_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:19.319108+00:00
-- url     : https://prove2.me/submissions/92fc1d3e-4079-4094-8289-66c10412aa49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
import Theorems.Thm_PI_Mk_nextCoeff_X_pow_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix
namespace PI.Mk
theorem _root_.solution (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) :
    Good ℓ (cyclotomic (ℓ ^ (j + 1)) ℚ) := by
  have := Fact.mk hℓ
  have h2 : 2 ≤ ℓ := hℓ.two_le
  have hmon : (cyclotomic (ℓ ^ (j + 1)) ℚ).Monic := cyclotomic.monic _ ℚ
  have hdeg : (cyclotomic (ℓ ^ (j + 1)) ℚ).natDegree = ℓ ^ j * (ℓ - 1) := by
    rw [natDegree_cyclotomic, Nat.totient_prime_pow_succ hℓ]
  have hm1 : ((X : ℚ[X]) ^ ℓ ^ j - 1).Monic := by
    simpa using monic_X_pow_sub_C (1 : ℚ) (pow_pos hℓ.pos j).ne'
  have hnc := congrArg nextCoeff
    (cyclotomic_prime_pow_mul_X_pow_sub_one (R := ℚ) (p := ℓ) (k := j))
  rw [hmon.nextCoeff_mul hm1, nextCoeff_X_pow_sub_one _ (pow_pos hℓ.pos j),
    nextCoeff_X_pow_sub_one _ (pow_pos hℓ.pos (j + 1))] at hnc
  have hne : ℓ ^ (j + 1) ≠ 1 := (Nat.one_lt_pow (by omega) hℓ.one_lt).ne'
  rw [if_neg hne] at hnc
  rcases j with _ | k
  · rw [pow_zero, if_pos rfl] at hnc
    refine ⟨hmon, 1, ?_, ?_, fun h => absurd h one_ne_zero⟩
    · rw [hdeg]; simp
    · have hc : (((ℓ ^ 0 * (ℓ - 1) : ℕ)) : ℚ) = (ℓ : ℚ) - 1 := by
        rw [pow_zero, one_mul, Nat.cast_sub (by omega), Nat.cast_one]
      rw [hdeg, hc]; push_cast; linarith
  · have hne' : ℓ ^ (k + 1) ≠ 1 := (Nat.one_lt_pow (by omega) hℓ.one_lt).ne'
    rw [if_neg hne'] at hnc
    have hz : nextCoeff (cyclotomic (ℓ ^ (k + 1 + 1)) ℚ) = 0 := by linarith
    refine ⟨hmon, ℓ ^ k * (ℓ - 1), ?_, ?_, ?_⟩
    · rw [hdeg]
      calc (ℓ - 1) * (ℓ ^ k * (ℓ - 1)) ≤ ℓ * (ℓ ^ k * (ℓ - 1)) :=
            Nat.mul_le_mul_right _ (Nat.sub_le ℓ 1)
        _ = ℓ ^ (k + 1) * (ℓ - 1) := by ring
    · rw [hdeg, hz]; push_cast; ring
    · intro h
      exact absurd h (mul_ne_zero (pow_ne_zero _ hℓ.ne_zero) (by omega))
end PI.Mk
