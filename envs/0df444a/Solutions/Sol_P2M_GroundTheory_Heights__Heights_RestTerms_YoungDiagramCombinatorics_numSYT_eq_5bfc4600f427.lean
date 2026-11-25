-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numSYT_eq_5bfc4600f427
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:40:21.64341+00:00
-- url     : https://prove2.me/submissions/d870ec71-cd3e-464a-bd0c-36fde5ec3fd9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_card_monotone_equiv_congr_f5634ff25944
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_numStandardTable_eq_card_monotone_c3531fff2cb2

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
theorem _root_.solution {r : ℕ} (la : Fin r → ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.numSYT la = RestTerms.numStandardTable la := by
  rw [numStandardTable_eq_card_monotone]
  unfold IndefiniteRowSideFullHecke.RestTerms.numSYT
  refine (card_monotone_equiv_congr (cellIso la) ?_).symm
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (cellIso la).toEquiv
end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
