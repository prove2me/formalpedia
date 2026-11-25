-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RectangleTablePos_proof_62ddc2e81a6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:30.297882+00:00
-- url     : https://prove2.me/submissions/542f2a10-8a1c-4075-92bc-ade1c5c31cc2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTablePos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RectangleTablePos_intersectionNumber_baseChange_ae6f04d8e84b

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
theorem _root_.solution (_h : FrobeniusDimensionFormula.Statement) :
    RectangleTablePos.Statement :=
  RectangleTablePos.intersectionNumber_baseChange
end RectangleTablePos
end GroundTheory.Heights₂.Heights.RestTerms
