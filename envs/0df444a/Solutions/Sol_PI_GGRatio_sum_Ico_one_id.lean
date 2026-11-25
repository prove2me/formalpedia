-- Prove2me | solution 1 for PI.GGRatio.sum_Ico_one_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:04.525108+00:00
-- url     : https://prove2.me/submissions/3cb869ba-06b9-4c03-b612-9f179b1dc98b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GenericRatioBound_GenericRatioOfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGRatio
open Finset
namespace PI.GGRatio
theorem _root_.solution (k : ℕ) : ∑ i ∈ Ico 1 k, i = k * (k - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [← Finset.sum_range_id, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
  simp
end PI.GGRatio
