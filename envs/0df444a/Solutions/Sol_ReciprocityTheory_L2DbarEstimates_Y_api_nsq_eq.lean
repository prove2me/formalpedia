-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.api_nsq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:35:05.50587+00:00
-- url     : https://prove2.me/submissions/11f36bfa-b522-409c-8d6a-3925210aed84

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeW
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeI

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
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la U F) {i : ι} {x : Y}
    (hxs : x ∈ (A.chart i).source) (hxU : x ∈ U) :
    ‖F i x‖ ^ 2 * Real.exp (-A.ph la i x) = A.nsq la F x := by
  unfold WeightedAtlas.nsq
  have hj : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hsec := hFs.2 i (A.pick x) x hxU hxs hj
  have hph := A.ph_trans la i (A.pick x) x hxs hj
  have hg := A.g_ne la i (A.pick x) x hxs hj
  have hgpos : 0 < ‖A.g la i (A.pick x) x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
  rw [hsec, hph, norm_mul, mul_pow,
    show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) =
      Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring,
    Real.exp_add, Real.exp_log hgpos]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
