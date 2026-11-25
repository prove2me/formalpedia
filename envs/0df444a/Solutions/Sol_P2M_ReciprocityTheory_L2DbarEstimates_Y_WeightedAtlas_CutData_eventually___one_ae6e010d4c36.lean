-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_eventually___one_ae6e010d4c36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:29:30.600257+00:00
-- url     : https://prove2.me/submissions/58812826-2759-45fc-8f6d-a2eee2a0b68f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_chiC_of_mem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isOpen_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_mem_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_trans_contDiffOn


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
theorem _root_.solution {P : Y} (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hyP : y ∈ (A.chart (A.pick P)).source)
    (hb : A.chart (A.pick P) y ∈ ball (A.chart (A.pick P) P) (D.r1 P)) :
    ∀ᶠ v in 𝓝 (A.chart j y), (A.chart j).symm v ∈ (A.chart (A.pick P)).source ∧
      D.χ P ((A.chart j).symm v) = 1 := by
  have hc : ContinuousOn ((A.chart (A.pick P)) ∘ (A.chart j).symm) (ovl A.chart j (A.pick P)) :=
    (A.trans_contDiffOn j (A.pick P)).continuousOn
  have hopen : IsOpen (ovl A.chart j (A.pick P) ∩ ((A.chart (A.pick P)) ∘ (A.chart j).symm) ⁻¹'
      ball (A.chart (A.pick P) P) (D.r1 P)) :=
    hc.isOpen_inter_preimage (A.isOpen_ovl j _) isOpen_ball
  have hmem : A.chart j y ∈ ovl A.chart j (A.pick P) ∩ ((A.chart (A.pick P)) ∘ (A.chart j).symm) ⁻¹'
      ball (A.chart (A.pick P) P) (D.r1 P) :=
    ⟨A.mem_ovl hj hyP, by simpa [Function.comp, (A.chart j).left_inv hj] using hb⟩
  filter_upwards [hopen.mem_nhds hmem] with v hv
  refine ⟨hv.1.2, ?_⟩
  rw [χ, A.chiC_of_mem hv.1.2]
  exact D.one P _ (ball_subset_closedBall hv.2)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
