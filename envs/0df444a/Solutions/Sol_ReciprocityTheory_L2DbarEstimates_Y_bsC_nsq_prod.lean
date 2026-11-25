-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsC_nsq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:48.482872+00:00
-- url     : https://prove2.me/submissions/ab290be7-ee55-4edc-a14a-151e077e277e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ph_nsmul


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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (la L : La) (m : ℕ) (q u v : ι → Y → ℂ) (c : ℂ) (y : Y)
    (hq : q (A.pick y) y = c * (u (A.pick y) y * v (A.pick y) y ^ m)) :
    A.nsq (la + m • L) q y = ‖c‖ ^ 2 * A.nsq la u y * A.nsq L v y ^ m := by
  unfold nsq
  rw [hq, A.ph_add la (m • L) _ y (A.mem_pick y), bsA_ph_nsmul A L m (A.mem_pick y)]
  rw [norm_mul, norm_mul, norm_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, neg_add,
    Real.exp_add, show -((m : ℝ) * A.ph L (A.pick y) y) = (m : ℝ) * (-A.ph L (A.pick y) y) by ring,
    Real.exp_nat_mul, ← pow_mul]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
