-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_homogSubmodule_eq_map_937d9ae32e0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:12.777181+00:00
-- url     : https://prove2.me/submissions/a834117a-ded9-4b4a-a7c0-1d4b0050eb2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_of_homog_e7fc05f7ee1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_homog_12fc29555f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_homog_6b1a42b630a2

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
theorem _root_.solution (M : K ⊕ Unit → ℕ) :
    weightedHomogeneousSubmodule F (blockWeight (Sum.elim ι ptIdx)) M =
      (weightedHomogeneousSubmodule F (blockWeight ι) (restrictFirst M)).map
        ((LinearMap.mulRight F (X newVar ^ M (.inr ()))).comp
          (rename (liftVar (ι := ι) ptIdx)).toLinearMap) := by
  ext g
  rw [mem_weightedHomogeneousSubmodule]
  constructor
  · intro hg
    refine ⟨aeval (dropPt F) g, ?_, ?_⟩
    · exact dropPt_homog hg
    · exact rename_dropPt_of_homog hg
  · rintro ⟨f, hf, rfl⟩
    have hf' : IsWeightedHomogeneous (blockWeight ι) f (restrictFirst M) := hf
    have h := (rename_homog hf').mul
      ((isWeightedHomogeneous_X F (blockWeight (Sum.elim ι ptIdx)) newVar).pow (M (.inr ())))
    have e : extendZero (restrictFirst M) +
        M (.inr ()) • blockWeight (Sum.elim ι ptIdx) newVar = M := by
      funext x
      rcases x with k | u
      · simp [extendZero, restrictFirst, blockWeight, newVar]
      · cases u
        simp [extendZero, restrictFirst, blockWeight, newVar]
    rw [e] at h
    exact h
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
