-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_fin_ne_zero_ad271659adeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:37.428852+00:00
-- url     : https://prove2.me/submissions/07cd7f33-da85-4bc8-bb96-4ac4e733a562

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFrobeniusCharacterFormula

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (r : ℕ) :
    vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) ≠ 0 := by
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  refine sub_ne_zero.mpr fun h => hij ?_
  exact X_injective (R := ℚ) h
end GroundTheory.Heights₂.Heights.RestTerms
