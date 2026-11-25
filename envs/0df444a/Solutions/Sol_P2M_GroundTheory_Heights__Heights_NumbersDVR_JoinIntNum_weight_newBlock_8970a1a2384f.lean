-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_weight_newBlock_8970a1a2384f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:39.465477+00:00
-- url     : https://prove2.me/submissions/2a45561f-7484-46b5-8af5-913366abdb6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum

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
theorem _root_.solution (d : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι ptIdx)) d (.inr ()) = d newVar := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [Finset.sum_eq_single newVar]
  · simp [blockWeight, newVar]
  · rintro ⟨k | u, i⟩ _ hne
    · simp [blockWeight]
    · exfalso
      apply hne
      cases u
      obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      rfl
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
