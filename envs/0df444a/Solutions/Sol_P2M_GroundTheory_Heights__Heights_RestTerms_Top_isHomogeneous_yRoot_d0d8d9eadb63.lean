-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_yRoot_d0d8d9eadb63
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:06.814569+00:00
-- url     : https://prove2.me/submissions/ee344c85-34cb-49bd-8238-ff4115ae19f1

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
theorem _root_.solution (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin r) :
    (yRoot f r a c τ i).IsHomogeneous 1 := by
  have := (isHomogeneous_C (Fin f × Fin (r + a)) c.sign).mul (isHomogeneous_X ℚ (yIndex f r a c τ i))
  simpa [yRoot] using this
end GroundTheory.Heights₂.Heights.RestTerms.Top
