-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RectangleTablePos_intersectionNumber_baseChange_ae6f04d8e84b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:59.31188+00:00
-- url     : https://prove2.me/submissions/6b8c2726-302b-48fb-bf8d-eac5e62697ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTablePos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_pos_e362a1d9e1a0

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
namespace RectangleTablePos
theorem _root_.solution : RectangleTablePos.Statement :=
  fun r a => numStandardTable_pos (rectangle r a)
end RectangleTablePos
end GroundTheory.Heights₂.Heights.RestTerms
