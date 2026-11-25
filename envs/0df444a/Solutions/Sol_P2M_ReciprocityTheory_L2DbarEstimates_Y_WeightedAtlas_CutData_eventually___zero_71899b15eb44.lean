-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___zero_71899b15eb44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:43.598684+00:00
-- url     : https://prove2.me/submissions/d82e2065-161e-4f4a-87cc-1902ba6473c8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_K_compact
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData___supp_82118ed35144

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
theorem _root_.solution {P : Y} (hP : P ∈ Sf) (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hy : y ∉ D.K P) : ∀ᶠ v in 𝓝 (A.chart j y), D.χ P ((A.chart j).symm v) = 0 := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (D.K P)ᶜ) :=
    (A.chart j).isOpen_inter_preimage_symm (D.K_compact hP).isClosed.isOpen_compl
  filter_upwards [hopen.mem_nhds ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hy]⟩]
    with v hv
  by_contra h; exact hv.2 (D.χ_supp P _ h)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
