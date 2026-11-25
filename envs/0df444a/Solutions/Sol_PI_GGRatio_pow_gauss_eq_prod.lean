-- Prove2me | solution 1 for PI.GGRatio.pow_gauss_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:37.5597+00:00
-- url     : https://prove2.me/submissions/ac8bea0b-6dee-4bfe-bc7e-ba0027173331

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GenericRatioBound_GenericRatioOfBound
import Theorems.Thm_PI_GGRatio_sum_Ico_one_id

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
theorem _root_.solution (q : ℝ) (k : ℕ) : q ^ (k * (k - 1) / 2) = ∏ i ∈ Ico 1 k, q ^ i := by
  rw [Finset.prod_pow_eq_pow_sum, sum_Ico_one_id]
end PI.GGRatio
