-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.KerSplit.isIntegral_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:48.110653+00:00
-- url     : https://prove2.me/submissions/370de7fd-0577-4a0f-a542-f776fb491acc

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
theorem _root_.solution {K : Type} [Field K] (d : ℕ) (s : K) (hs : s * s = -(d : K)) :
    IsIntegral ℤ s := by
  refine ⟨X ^ 2 + C (d : ℤ), monic_X_pow_add_C _ two_ne_zero, ?_⟩
  have e : (algebraMap ℤ K) (d : ℤ) = (d : K) := by simp
  rw [eval₂_add, eval₂_X_pow, eval₂_C, e]
  linear_combination hs
end PI.UnitaryGroupMassFormula.KerSplit
