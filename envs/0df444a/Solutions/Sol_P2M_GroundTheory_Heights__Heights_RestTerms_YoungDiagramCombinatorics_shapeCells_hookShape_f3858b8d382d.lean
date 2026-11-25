-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_shapeCells_hookShape_f3858b8d382d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:15.415063+00:00
-- url     : https://prove2.me/submissions/8ce53b25-ac13-42bc-9159-ab4ba431ff01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone

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
    IndefiniteRowSideFullHecke.RestTerms.shapeCells (IndefiniteRowSideFullHecke.RestTerms.hookShape k b) =
      IndefiniteRowSideFullHecke.RestTerms.shapeCells (RestTerms.hookShape r k b) := by
  ext x
  rw [mem_shapeCells, mem_shapeCells]
  simp only [RestTerms.hookShape, IndefiniteRowSideFullHecke.RestTerms.hookShape]
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨by omega, ?_⟩
    split_ifs at hx ⊢ <;> omega
  · rintro ⟨h, hx⟩
    have h' : x.1 < b + 1 := by
      by_contra hc
      split_ifs at hx <;> omega
    refine ⟨h', ?_⟩
    split_ifs at hx ⊢ <;> omega
end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
