-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.d_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:47.370198+00:00
-- url     : https://prove2.me/submissions/49489fc6-f4eb-4bff-a25d-ccfb54889c95

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
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
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
private theorem isChart_choose_and_symm_apply {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (x : M)
    (h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    IsChart n z (Classical.choose h) ∧ z x ∈ (Classical.choose h).target ∧
      (Classical.choose h).symm (z x) = x := by
  obtain ⟨he, hx⟩ := Classical.choose_spec h
  refine ⟨he, ?_, ?_⟩
  · rw [he hx]; exact (Classical.choose h).map_source hx
  · rw [he hx]; exact (Classical.choose h).left_inv hx
private theorem d_eq_wd_comp_chosen_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    d n z j f x = wd n j (f ∘ (Classical.choose h).symm) (z x) := by
  simp only [d, dif_pos h]
private theorem differentiableAt_comp_chart_symm_of_mem_target {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (w : V n)
    (hw : w ∈ e.target) : DifferentiableAt ℝ (f ∘ e.symm) w :=
  ((hf e he).differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds hw)
private theorem wd_wdb_const_mul (n : ℕ) (j : Fin n) (c : ℂ) {F : V n → ℂ} {w : V n}
    (hF : DifferentiableAt ℝ F w) :
    wd n j (fun y => c * F y) w = c * wd n j F w ∧
    wdb n j (fun y => c * F y) w = c * wdb n j F w := by
  have h1 : HasFDerivAt (fun y => c * F y) _ w := hF.hasFDerivAt.const_mul c
  refine ⟨?_, ?_⟩ <;>
    simp only [wd, wdb, h1.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) (f : M → ℂ) (hf : Ck n z 1 f) (j : Fin n) (x : M) :
    d n z j (fun y => c * f y) x = c * d n z j f x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [d_eq_wd_comp_chosen_chart_symm n z j _ x h, d_eq_wd_comp_chosen_chart_symm n z j f x h]
    exact (wd_wdb_const_mul n j c (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht)).1
  · simp [d, db, h]
end ReciprocityTheory.L2DbarEstimates
