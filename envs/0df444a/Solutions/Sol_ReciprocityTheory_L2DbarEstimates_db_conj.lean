-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.db_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:38.821119+00:00
-- url     : https://prove2.me/submissions/687e5e6e-0cf5-42ec-8daf-991ec42128ed

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
private theorem db_eq_wdb_comp_chosen_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source) :
    db n z j f x = wdb n j (f ∘ (Classical.choose h).symm) (z x) := by
  simp only [db, dif_pos h]
private theorem wdb_conj_eq_conj_wd_and_wd_conj (n : ℕ) (j : Fin n) (F : V n → ℂ) (w : V n) :
    wdb n j (fun y => (starRingEnd ℂ) (F y)) w = (starRingEnd ℂ) (wd n j F w) ∧
    wd n j (fun y => (starRingEnd ℂ) (F y)) w = (starRingEnd ℂ) (wdb n j F w) := by
  have h1 : (fun y => (starRingEnd ℂ) (F y)) = Complex.conjCLE ∘ F := by funext y; simp
  have h2 : ∀ v, fderiv ℝ (fun y => (starRingEnd ℂ) (F y)) w v = (starRingEnd ℂ) (fderiv ℝ F w v) := by
    intro v; rw [h1, Complex.conjCLE.comp_fderiv]; simp
  refine ⟨?_, ?_⟩ <;>
    simp only [wd, wdb, h2, map_div₀, map_sub, map_add, map_mul, Complex.conj_I, map_ofNat] <;> ring
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (j : Fin n) (x : M) :
    db n z j (fun y => (starRingEnd ℂ) (f y)) x = (starRingEnd ℂ) (d n z j f x) := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, d_eq_wd_comp_chosen_chart_symm n z j f x h]
    exact (wdb_conj_eq_conj_wd_and_wd_conj n j (f ∘ (Classical.choose h).symm) (z x)).1
  · simp [d, db, h]
end ReciprocityTheory.L2DbarEstimates
