-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.holoWeak_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:24.913858+00:00
-- url     : https://prove2.me/submissions/700b689d-6925-40e5-92c5-9f57b13ec459

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_Lemmata_MiscLemmasF_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Theorems.Thm_Bl_SecondBlockLemmaG_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {Ω K : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω)
    (hu : DifferentiableOn ℂ u Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (v : V n) :
    ∃ C : ℝ, ∀ x ∈ K, ‖fderiv ℝ u x v‖ ≤ C := by
  first | exact Bl.SecondBlockLemmaG.goal1 .. | (apply Bl.SecondBlockLemmaG.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaG.goal1 <;> assumption)
end ReciprocityTheory.L2DbarEstimates.C
