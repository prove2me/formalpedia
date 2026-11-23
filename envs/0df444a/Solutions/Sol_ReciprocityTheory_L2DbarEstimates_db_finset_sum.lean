-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.db_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:29.317847+00:00
-- url     : https://prove2.me/submissions/bae3ff8b-5a24-4e9e-974f-8dbf544955b8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
private theorem wd_wdb_finset_sum {ι : Type*} {n : ℕ} (s : Finset ι) (G : ι → V n → ℂ) (y : V n)
    (hG : ∀ i ∈ s, DifferentiableAt ℝ (G i) y) (j : Fin n) :
    wd n j (fun w => ∑ i ∈ s, G i w) y = ∑ i ∈ s, wd n j (G i) y ∧
      wdb n j (fun w => ∑ i ∈ s, G i w) y = ∑ i ∈ s, wdb n j (G i) y := by
  have hF : fderiv ℝ (fun w => ∑ i ∈ s, G i w) y = ∑ i ∈ s, fderiv ℝ (G i) y := by
    have H := HasFDerivAt.sum (u := s) (A := G) fun i hi => (hG i hi).hasFDerivAt
    try simp only [Finset.sum_fn] at H
    exact H.fderiv
  constructor
  · simp only [wd, hF, ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_div]
  · simp only [wdb, hF, ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (F : ι → M → ℂ) (hF : ∀ i, Ck n z 1 (F i)) (j : Fin n) (x : M) :
    db n z j (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, db n z j (F i) x := by
  unfold db
  split_ifs with h
  · obtain ⟨hc, hxc⟩ := Classical.choose_spec h
    have hzx : z x ∈ (Classical.choose h).target := by
      rw [hc hxc]; exact (Classical.choose h).map_source hxc
    exact (wd_wdb_finset_sum s (fun i => F i ∘ (Classical.choose h).symm) (z x)
      (fun i _ => ((hF i _ hc).contDiffAt ((Classical.choose h).open_target.mem_nhds hzx)).differentiableAt
        one_ne_zero) j).2
  · simp
end ReciprocityTheory.L2DbarEstimates
