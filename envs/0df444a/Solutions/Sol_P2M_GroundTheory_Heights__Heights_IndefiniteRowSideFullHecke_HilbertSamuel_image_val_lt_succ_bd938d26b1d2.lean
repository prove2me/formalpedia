-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_image_val_lt_succ_bd938d26b1d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:57:26.070634+00:00
-- url     : https://prove2.me/submissions/c74ce23b-8497-4a2f-b58d-5c91d9392913

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution {α : Type*} {n : ℕ} (x : Fin n → α) (j : Fin n) :
    x '' {i | i.val < j.val + 1} = insert (x j) (x '' {i | i.val < j.val}) := by
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact Or.inr ⟨i, h, rfl⟩
    · exact Or.inl (by rw [Fin.ext h])
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨j, Nat.lt_succ_self _, rfl⟩
    · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
