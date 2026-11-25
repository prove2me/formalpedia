-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_bound_of_eventually_613d97591c0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:33.361317+00:00
-- url     : https://prove2.me/submissions/14af8fb9-80ef-40f2-89d8-bf5ccbcbb794

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections
theorem _root_.solution (f : ℕ → ℝ) (r : ℝ) (a₀ : ℕ) (C : ℝ)
    (h : ∀ n, a₀ ≤ n → |f n| ≤ C * ((n : ℝ) + 1) ^ r) :
    ∃ C' : ℝ, ∀ n : ℕ, |f n| ≤ C' * ((n : ℝ) + 1) ^ r := by
  refine ⟨max C (∑ k ∈ Finset.range a₀, |f k| / ((k : ℝ) + 1) ^ r), fun n => ?_⟩
  have hp : 0 < ((n : ℝ) + 1) ^ r := by positivity
  rcases le_or_gt a₀ n with hn | hn
  · exact (h n hn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  · have h1 : |f n| / ((n : ℝ) + 1) ^ r ≤ ∑ k ∈ Finset.range a₀, |f k| / ((k : ℝ) + 1) ^ r :=
      Finset.single_le_sum (f := fun k => |f k| / ((k : ℝ) + 1) ^ r)
        (fun k _ => by positivity) (Finset.mem_range.2 hn)
    calc |f n| = |f n| / ((n : ℝ) + 1) ^ r * ((n : ℝ) + 1) ^ r := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (h1.trans (le_max_right _ _)) hp.le
end GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections
