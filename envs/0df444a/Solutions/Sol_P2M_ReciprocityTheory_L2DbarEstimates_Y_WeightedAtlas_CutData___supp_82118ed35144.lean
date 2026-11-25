-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___supp_82118ed35144
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:05.199325+00:00
-- url     : https://prove2.me/submissions/3bf3643c-c9a5-4b88-986d-71666a3cb75a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_chiC_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
variable {A}
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
variable {Sf : Finset Y} (D : CutData A Sf)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
theorem _root_.solution (P : Y) (y : Y) (hy : D.χ P y ≠ 0) : y ∈ D.K P := by
  by_contra h; exact hy (A.chiC_eq_zero (D.supp P) h)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
