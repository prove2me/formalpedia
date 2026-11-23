-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.db_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:32.831949+00:00
-- url     : https://prove2.me/submissions/997fed98-4aa6-4cc8-b012-30773954c2f7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
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
private theorem db_eq_wdb_comp_chosen_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    db n z j f x = wdb n j (f ∘ (Classical.choose h).symm) (z x) := by
  simp only [db, dif_pos h]
private theorem differentiableAt_comp_chart_symm_of_mem_target {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (w : V n)
    (hw : w ∈ e.target) : DifferentiableAt ℝ (f ∘ e.symm) w :=
  ((hf e he).differentiableOn (by simp)).differentiableAt (e.open_target.mem_nhds hw)
private theorem wd_wdb_add_and_mul (n : ℕ) (j : Fin n) {F G : V n → ℂ} {w : V n}
    (hF : DifferentiableAt ℝ F w) (hG : DifferentiableAt ℝ G w) :
    wd n j (fun y => F y + G y) w = wd n j F w + wd n j G w ∧
    wdb n j (fun y => F y + G y) w = wdb n j F w + wdb n j G w ∧
    wd n j (fun y => F y * G y) w = wd n j F w * G w + F w * wd n j G w ∧
    wdb n j (fun y => F y * G y) w = wdb n j F w * G w + F w * wdb n j G w := by
  have h1 : HasFDerivAt (fun y => F y + G y) _ w := hF.hasFDerivAt.add hG.hasFDerivAt
  have h2 : HasFDerivAt (fun y => F y * G y) _ w := hF.hasFDerivAt.mul hG.hasFDerivAt
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [wd, wdb, h1.fderiv, h2.fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    db n z j (fun y => f y * g y) x = db n z j f x * g x + f x * db n z j g x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    have hx' : ∀ F : M → ℂ, (F ∘ (Classical.choose h).symm) (z x) = F x := fun F => by simp [hsx]
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, db_eq_wdb_comp_chosen_chart_symm n z j f x h, db_eq_wdb_comp_chosen_chart_symm n z j g x h]
    refine (wd_wdb_add_and_mul n j (differentiableAt_comp_chart_symm_of_mem_target n z f hf _ he _ ht) (differentiableAt_comp_chart_symm_of_mem_target n z g hg _ he _ ht)).2.2.2.trans ?_
    rw [hx' f, hx' g]
  · simp [d, db, h]
end ReciprocityTheory.L2DbarEstimates
