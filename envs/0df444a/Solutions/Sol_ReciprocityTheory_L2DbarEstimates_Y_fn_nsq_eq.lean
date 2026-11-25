-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_nsq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:47.849862+00:00
-- url     : https://prove2.me/submissions/e603df84-ee31-4e27-ac84-e5bd0e1e4a18

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {la : La} {U : Set Y} {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) {i : ι} {x : Y}
    (hxs : x ∈ (A.chart i).source) (hxU : x ∈ U) :
    ‖F i x‖ ^ 2 * Real.exp (-A.ph la i x) = A.nsq la F x := by
  unfold WeightedAtlas.nsq
  have hj : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hg : 0 < ‖A.g la i (A.pick x) x‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (A.g_ne la i (A.pick x) x hxs hj)) 2
  rw [hFs.2 i (A.pick x) x hxU hxs hj, A.ph_trans la i (A.pick x) x hxs hj,
    show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) =
      Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring,
    Real.exp_add, Real.exp_log hg, norm_mul]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
