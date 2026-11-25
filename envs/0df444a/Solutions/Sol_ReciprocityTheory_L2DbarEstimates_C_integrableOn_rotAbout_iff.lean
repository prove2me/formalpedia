-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.integrableOn_rotAbout_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:29.477077+00:00
-- url     : https://prove2.me/submissions/0e7f8c4c-bd0e-4045-8973-b618f947fbbd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurePreserving_rotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurableEmbedding_rotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_indicator_rotAbout

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
theorem _root_.solution {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    {E : Type*} [NormedAddCommGroup E] (g : V n → E) :
    IntegrableOn (fun z => g (rotAbout c a z)) (ball c R) ↔ IntegrableOn g (ball c R) := by
  rw [← integrable_indicator_iff measurableSet_ball, ← integrable_indicator_iff measurableSet_ball]
  have : (ball c R).indicator (fun z => g (rotAbout c a z)) =
      (ball c R).indicator g ∘ rotAbout c a :=
    funext fun z => indicator_rotAbout c ha R g z
  rw [this]
  exact (measurePreserving_rotAbout c ha).integrable_comp_emb (measurableEmbedding_rotAbout c ha)
end ReciprocityTheory.L2DbarEstimates.C
