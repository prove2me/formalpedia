-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_hookShape_4cc1d79bbf5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:17.633772+00:00
-- url     : https://prove2.me/submissions/d5a29010-7fc2-4d45-aa23-28a6c7d70c18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_eq_5bfc4600f427
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_shapeCells_hookShape_f3858b8d382d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
theorem _root_.solution (r k b : ℕ) (hb : b < r) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      RestTerms.numStandardTable (RestTerms.hookShape r k b) := by
  rw [← numSYT_eq]
  unfold IndefiniteRowSideFullHecke.RestTerms.numSYT
  rw [shapeCells_hookShape r k b hb]
end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
