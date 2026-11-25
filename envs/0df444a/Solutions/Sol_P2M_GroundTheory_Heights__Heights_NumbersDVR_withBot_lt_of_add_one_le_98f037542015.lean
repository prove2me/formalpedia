-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_le_98f037542015
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:52.995393+00:00
-- url     : https://prove2.me/submissions/877326f4-a490-4a18-b044-b2744c5d3233

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_le_of_add_one_le_a9caad75ac39

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < ((N + 1 : ℕ) : WithBot ℕ∞) := by
  refine lt_of_le_of_lt (withBot_le_of_add_one_le x N hx) ?_
  exact_mod_cast Nat.lt_succ_self N
end GroundTheory.Heights₂.Heights.NumbersDVR
