-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_bot_of_not_isRelevant_05c8187c8ccb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:26.301035+00:00
-- url     : https://prove2.me/submissions/0583959c-c7d1-4005-be57-3f2053f63558

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbIrrelevantZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_isMultiHomog_of_block_le_2330e40a8e11

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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : ¬ IsRelevant I)
    {m : K → ℕ} (hm : ∀ k, 1 ≤ m k) : gradedPiece I m = ⊥ := by
  obtain ⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I := by
    by_contra h
    exact hI fun k => by
      by_contra h'
      exact h ⟨k, fun i => by
        by_contra h''
        exact h' ⟨i, h''⟩⟩
  rw [eq_bot_iff]
  rintro _ ⟨f, hf, rfl⟩
  rw [Submodule.mem_bot]
  have : f ∈ I := mem_of_isMultiHomog_of_block_le hk (hm k)
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
  simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr this
end GroundTheory.Heights₂.Heights.FieldNumbers
