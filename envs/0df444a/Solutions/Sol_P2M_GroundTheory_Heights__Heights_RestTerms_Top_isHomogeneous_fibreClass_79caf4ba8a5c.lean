-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_fibreClass_79caf4ba8a5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:12.907931+00:00
-- url     : https://prove2.me/submissions/42f5b8d5-7e04-4c40-aefe-15b18fade98e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_yRoot_d0d8d9eadb63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_zRoot_2e26d449e5d7

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
theorem _root_.solution (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ)
    (c : SmallBlock) :
    (fibreClass f r a c).IsHomogeneous (f * (r * (r - 1) / 2 + a * (a - 1) / 2)) := by
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
    (fun τ => vandermondeOf (yRoot f r a c τ) * vandermondeOf (zRoot f r a c τ))
    (fun _ => r * (r - 1) / 2 + a * (a - 1) / 2)
    (fun τ _ => (hV _ ℚ r _ (isHomogeneous_yRoot f r a c τ)).mul
      (hV _ ℚ a _ (isHomogeneous_zRoot f r a c τ)))
  simpa [fibreClass, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h
end GroundTheory.Heights₂.Heights.RestTerms.Top
