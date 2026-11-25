-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mollify_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:27:32.663147+00:00
-- url     : https://prove2.me/submissions/348e186c-6589-4e8d-833d-cc0c9f97805b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegIndep
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mollify_mollify_swap
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_conv_symm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_mean
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mollify_differentiableAt


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
theorem _root_.solution {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} {s t : ℝ} {x : V n}
    (hΩ : IsOpen Ω) (hu : Integrable u) (hw : WeakHolo Ω u) (hs : 0 < s) (ht : 0 < t)
    (hx : closedBall x (s + t) ⊆ Ω) :
    mollify n s u x = mollify n t u x := by
  have hA : DifferentiableOn ℂ (mollify n t u) (ball x s) := by
    intro w hwb
    rw [Metric.mem_ball] at hwb
    refine (mollify_differentiableAt hΩ hu hw ht ((Metric.closedBall_subset_closedBall' ?_).trans hx)).differentiableWithinAt
    linarith
  have hB : DifferentiableOn ℂ (mollify n s u) (ball x t) := by
    intro w hwb
    rw [Metric.mem_ball] at hwb
    refine (mollify_differentiableAt hΩ hu hw hs ((Metric.closedBall_subset_closedBall' ?_).trans hx)).differentiableWithinAt
    linarith
  calc mollify n s u x = ∫ w, (moll n t (x - w) : ℂ) * mollify n s u w := (moll_mean ht hB).symm
    _ = ∫ y, ((∫ w, moll n t (x - w) * moll n s (w - y) : ℝ) : ℂ) * u y :=
        mollify_mollify_swap hu ht hs x
    _ = ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
        congr 1; funext y; rw [moll_conv_symm n t s x y]
    _ = ∫ w, (moll n s (x - w) : ℂ) * mollify n t u w := (mollify_mollify_swap hu hs ht x).symm
    _ = mollify n t u x := moll_mean hs hA
end ReciprocityTheory.L2DbarEstimates.C
