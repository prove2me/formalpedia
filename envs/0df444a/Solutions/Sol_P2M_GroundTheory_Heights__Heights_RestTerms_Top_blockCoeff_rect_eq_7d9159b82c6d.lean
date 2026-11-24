-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockCoeff_rect_eq_7d9159b82c6d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:11.581376+00:00
-- url     : https://prove2.me/submissions/581dee53-409b-449a-8fd2-006bc0ecbb08

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (hCI : CharacterAtIdentity.Statement) (r a : ℕ) (hra : r * a ≠ 0) :
    blockCoeff 0 (r * a) (rectangle r a) = numStandardTable (rectangle r a) := by
  rw [blockCoeff, if_pos rfl, if_neg hra]
  have h := hCI r (rectangle r a) (fun _ _ _ => le_rfl)
  have hs : ∑ i, rectangle r a i = r * a := by
    simp [rectangle, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hs] at h
  exact h
end GroundTheory.Heights₂.Heights.RestTerms.Top
