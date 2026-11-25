-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_homog_12fc29555f54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:38.377909+00:00
-- url     : https://prove2.me/submissions/fbe520a7-7b91-4091-ad54-8fb01e58b7cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_isWeightedHomogeneous_algHom_7ac893965c47

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution {f : MRing ι F} {m : K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f m) :
    IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx))
      (rename (liftVar (ι := ι) ptIdx) f) (extendZero m) := by
  refine isWeightedHomogeneous_algHom _ _ extendZero _ (fun s => ?_) hf
  rw [rename_X]
  have e : extendZero (blockWeight ι s) = blockWeight (Sum.elim ι ptIdx) (liftVar (ι := ι) ptIdx s) := by
    funext x
    rcases x with k | u
    · simp [extendZero, blockWeight, liftVar, Pi.single_apply]
    · simp [extendZero, blockWeight, liftVar]
  rw [e]
  exact isWeightedHomogeneous_X F _ _
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
