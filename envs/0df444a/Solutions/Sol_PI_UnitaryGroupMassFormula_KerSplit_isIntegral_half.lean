-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.KerSplit.isIntegral_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:45.527574+00:00
-- url     : https://prove2.me/submissions/746fc341-5c92-48a6-954a-e5d271d44b92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KernelSplitting_IsIntegralHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.KerSplit
namespace PI.UnitaryGroupMassFormula.KerSplit
theorem _root_.solution {K : Type} [Field K] [CharZero K] (d : ℕ) (s : K) (hd : d % 8 = 7)
    (hs : s * s = -(d : K)) : IsIntegral ℤ ((1 + s) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hkK : (d : K) + 1 = 4 * (k : K) := by exact_mod_cast hk
  refine ⟨X ^ 2 - X + C (k : ℤ), ?_, ?_⟩
  · have e : (X ^ 2 - X + C (k : ℤ) : ℤ[X]) = X ^ 2 - (X - C (k : ℤ)) := by ring
    rw [e]
    apply monic_X_pow_sub
    rw [degree_X_sub_C]
    exact WithBot.coe_lt_coe.mpr (by norm_num)
  · have e : (algebraMap ℤ K) (k : ℤ) = (k : K) := by simp
    rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, e]
    linear_combination (1 / 4 : K) * hs - (1 / 4 : K) * hkK
end PI.UnitaryGroupMassFormula.KerSplit
