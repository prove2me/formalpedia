-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_antisymmetrize_1230b0a0ab9c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:03:02.241184+00:00
-- url     : https://prove2.me/submissions/2cf1fe66-93b1-4c8a-9643-c3a1b555a8b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_antisymmetrize_63f7c060ed6c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f N : ℕ) (H : RootRing f N) :
    IsBlockAlternating f N (antisymmetrize f N H) :=
  fun w => Flag.blockPermute_antisymmetrize f N w H
end GroundTheory.Heights₂.Heights.RestTerms
