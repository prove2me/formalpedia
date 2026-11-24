-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_le_of_add_one_le_a9caad75ac39
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.601052+00:00
-- url     : https://prove2.me/submissions/f9368dcb-79f6-41b1-9223-bda889ed43cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Theorems.Thm_UpperTheory_Reformulated_B_Qn14_le_of_add_one_le_succ


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
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ ((N : ℕ) : WithBot ℕ∞) :=
  by apply _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ <;> assumption
end GroundTheory.Heights₂.Heights.NumbersDVR
