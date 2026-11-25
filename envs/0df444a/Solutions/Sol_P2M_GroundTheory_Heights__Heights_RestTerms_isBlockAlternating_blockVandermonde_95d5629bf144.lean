-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_blockVandermonde_95d5629bf144
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:54.58082+00:00
-- url     : https://prove2.me/submissions/f29abfea-10cd-48f2-a0a9-a799fd567587

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e


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
theorem _root_.solution (f N : ℕ) :
    IsBlockAlternating f N (blockVandermonde f N) :=
  fun w => Flag.blockPermute_blockVandermonde f N w
end GroundTheory.Heights₂.Heights.RestTerms
