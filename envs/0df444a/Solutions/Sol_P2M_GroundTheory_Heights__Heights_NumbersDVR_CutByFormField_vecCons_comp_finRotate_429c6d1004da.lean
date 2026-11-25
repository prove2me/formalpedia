-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByFormField_vecCons_comp_finRotate_429c6d1004da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:25.383466+00:00
-- url     : https://prove2.me/submissions/e4ced353-8880-4e03-bc65-5f8e63240361

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByFormField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.CutByFormField
namespace GroundTheory.Heights₂.Heights.NumbersDVR.CutByFormField
theorem _root_.solution {α : Type*} {n : ℕ} (c : α) (bs : Fin n → α) :
    Matrix.vecCons c bs ∘ finRotate (n + 1) = Fin.snoc (α := fun _ => α) bs c := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · rw [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.snoc_castSucc,
      Matrix.cons_val_succ]
end GroundTheory.Heights₂.Heights.NumbersDVR.CutByFormField
