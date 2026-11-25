-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:26.870782+00:00
-- url     : https://prove2.me/submissions/6ff1b560-cee9-4af7-b438-0567507f0efb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) {κ : Type*} (F : Finset κ)
    (h : κ → ι → Y → ℂ) (y : Y) :
    A.nsq la (fun i y => ∑ q ∈ F, h q i y) y ≤ (F.card : ℝ) * ∑ q ∈ F, A.nsq la (h q) y := by
  unfold nsq
  have h1 : ‖∑ q ∈ F, h q (A.pick y) y‖ ^ 2 ≤ (F.card : ℝ) * ∑ q ∈ F, ‖h q (A.pick y) y‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq
  have he : 0 ≤ Real.exp (-A.ph la (A.pick y) y) := (Real.exp_pos _).le
  calc ‖∑ q ∈ F, h q (A.pick y) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y) y)
      ≤ ((F.card : ℝ) * ∑ q ∈ F, ‖h q (A.pick y) y‖ ^ 2) * Real.exp (-A.ph la (A.pick y) y) :=
        mul_le_mul_of_nonneg_right h1 he
    _ = _ := by rw [mul_assoc, Finset.sum_mul]
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
