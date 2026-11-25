-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.entire_poly_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:36.721115+00:00
-- url     : https://prove2.me/submissions/824b54b8-b234-459b-9a20-96a03b34d436

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Lemmata_IterateZero_IterZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_OnePolyGrowth
import Theorems.Thm_Bl_IterateZero_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Filter Topology Function Metric Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (k : ℕ) : ∀ (g : ℂ → ℂ) (A : ℝ), Differentiable ℂ g →
    (∀ t, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t, g t = P.eval t := by
  first | exact Bl.IterateZero.goal1 .. | (apply Bl.IterateZero.goal1 <;> assumption) | (intros; apply Bl.IterateZero.goal1 <;> assumption)
end ReciprocityTheory.MultiplicativeHeights
