-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_le_sum_eq_60ecb16347c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:13.984267+00:00
-- url     : https://prove2.me/submissions/84f384dd-5ba3-47a8-bdab-971f517f834e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
namespace GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
theorem _root_.solution {α : Type} [Fintype α] (f : α → ℕ) :
    ∀ a : ℕ, a ≤ ∑ i, f i → ∃ g : α → ℕ, g ≤ f ∧ ∑ i, g i = a := by
  classical
  intro a
  induction a with
  | zero => exact fun _ ↦ ⟨0, fun _ ↦ Nat.zero_le _, by simp⟩
  | succ a ih =>
    intro ha
    obtain ⟨g, hg, hs⟩ := ih (by omega)
    have hex : ∃ i, g i < f i := by
      by_contra h
      push Not at h
      have : ∑ i, f i ≤ ∑ i, g i := Finset.sum_le_sum fun i _ ↦ h i
      omega
    obtain ⟨i, hi⟩ := hex
    refine ⟨Function.update g i (g i + 1), fun j ↦ ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        omega
      · simp only [Function.update_of_ne hj]
        exact hg j
    · rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)] at hs
      omega
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
