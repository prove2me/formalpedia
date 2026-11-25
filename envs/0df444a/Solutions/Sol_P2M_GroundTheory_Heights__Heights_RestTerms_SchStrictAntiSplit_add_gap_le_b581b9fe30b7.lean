-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_add_gap_le_b581b9fe30b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:00.10368+00:00
-- url     : https://prove2.me/submissions/e919783f-2f70-4dd0-8042-50fb89edf82d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AddGapLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchStrictAntiSplit
import Theorems.Thm_UpperTheory_Reformulated_B_Yoa4_add_gap_le


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
theorem _root_.solution {r : ℕ} {d : Fin r → ℕ} (hd : StrictAnti d) :
    ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k → d j + k ≤ d i :=
  _root_.UpperTheory.Reformulated.B.Yoa4.add_gap_le hd
end SchStrictAntiSplit
end GroundTheory.Heights₂.Heights.RestTerms
