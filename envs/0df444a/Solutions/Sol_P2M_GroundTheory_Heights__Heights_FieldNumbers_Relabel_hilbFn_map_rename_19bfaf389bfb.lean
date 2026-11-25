-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_hilbFn_map_rename_19bfaf389bfb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:30.426497+00:00
-- url     : https://prove2.me/submissions/07ef5780-6689-4961-916f-3dfff227cc71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_finrank_gradedPiece_map_rename_8357dad9eb33
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*}
  (e : K₁ ≃ K₂) (φ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hφ : ∀ v, (φ v).1 = e v.1)
  {F : Type*} [Field F]
include hφ
namespace GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
theorem _root_.solution (I : Ideal (MRing ι₁ F)) (m : K₂ → ℤ) :
    hilbFn (I.map (renameEquiv F φ)) m = hilbFn I (m ∘ e) := by
  unfold hilbFn
  have hpos : (∀ k, 0 ≤ m k) ↔ ∀ k, 0 ≤ (m ∘ e) k :=
    ⟨fun h k => h (e k), fun h k => by simpa using h (e.symm k)⟩
  by_cases h : ∀ k, 0 ≤ m k
  · rw [if_pos h, if_pos (hpos.1 h)]
    exact congrArg _ (finrank_gradedPiece_map_rename e φ hφ I (fun k => (m k).toNat))
  · rw [if_neg h, if_neg (mt hpos.2 h)]
end GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
