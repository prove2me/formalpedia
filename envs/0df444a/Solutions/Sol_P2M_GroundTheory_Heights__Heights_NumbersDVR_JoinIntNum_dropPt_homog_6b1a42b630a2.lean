-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_dropPt_homog_6b1a42b630a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:46.912446+00:00
-- url     : https://prove2.me/submissions/57bfa760-c83d-42d6-a1f6-a8da54ab6856

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
theorem _root_.solution {g : MRing (Sum.elim ι ptIdx) F} {M : K ⊕ Unit → ℕ}
    (hg : IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx)) g M) :
    IsWeightedHomogeneous (blockWeight ι) (aeval (dropPt F) g) (restrictFirst M) := by
  refine isWeightedHomogeneous_algHom _ _ restrictFirst _ (fun s => ?_) hg
  rw [aeval_X]
  rcases s with ⟨k | u, i⟩
  · have e : restrictFirst (blockWeight (Sum.elim ι ptIdx) ⟨.inl k, i⟩) =
        blockWeight ι (⟨k, i⟩ : Σ k, ι k) := by
      funext k'
      simp [restrictFirst, blockWeight, Pi.single_apply]
    rw [e]
    exact isWeightedHomogeneous_X F _ _
  · have e : restrictFirst (blockWeight (Sum.elim ι ptIdx) ⟨.inr u, i⟩) = 0 := by
      funext k'
      simp [restrictFirst, blockWeight]
    rw [e]
    exact isWeightedHomogeneous_one F _
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
