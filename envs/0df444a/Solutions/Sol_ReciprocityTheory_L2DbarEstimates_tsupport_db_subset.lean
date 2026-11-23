-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.tsupport_db_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:49.231695+00:00
-- url     : https://prove2.me/submissions/987c64c0-e12d-4e33-9b12-88faa01d8a78

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
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
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (f : M → ℂ) :
    tsupport (db n z j f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra hxs
  rw [Function.mem_support] at hx
  apply hx
  have hf0 : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxs
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [db_eq_wdb_comp_chosen_chart_symm n z j f x h]
    have h2 : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z x)] (fun _ => (0 : ℂ)) := by
      have hc := (Classical.choose h).continuousAt_symm ht
      rw [← hsx] at hf0
      exact hc.eventually hf0
    simp only [wdb, h2.fderiv_eq]
    simp
  · simp [db, h]
end ReciprocityTheory.L2DbarEstimates
