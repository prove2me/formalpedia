-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:47.778392+00:00
-- url     : https://prove2.me/submissions/3cfcc257-983e-4451-99a6-38888ca262e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_card_le_ringKrullDim_d0af2d24d2d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_lt_top_f6ad9b5ae3d3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution [Fintype K] [∀ k, Fintype (ι k)] {Q : Ideal (MRing ι F)}
    [Q.IsPrime] (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q)
    (hrel : IsRelevant Q) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRing ι F ⧸ Q) = D := by
  have h1 := card_le_ringKrullDim hQ hrel
  have h2 := ringKrullDim_lt_top Q
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ringKrullDim (MRing ι F ⧸ Q) = D := by
    cases h : ringKrullDim (MRing ι F ⧸ Q) with
    | bot =>
      rw [h] at h1
      exact absurd h1 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [h] at h2
        exact absurd h2 (by simp)
      | coe D => exact ⟨D, rfl⟩
  refine ⟨D, ?_, hD⟩
  rw [hD] at h1
  exact_mod_cast h1
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
