-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_sum_staircase_97112d8ec57a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:01.162056+00:00
-- url     : https://prove2.me/submissions/5d07bbb8-b381-4763-8bef-ec08427d6cb5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AddGapLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchStrictAntiSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchStrictAntiSplit
theorem _root_.solution (r : ℕ) :
    ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, Finset.sum_range_reflect (fun i => i) r,
    Finset.sum_range_id]
end SchStrictAntiSplit
end GroundTheory.Heights₂.Heights.RestTerms
