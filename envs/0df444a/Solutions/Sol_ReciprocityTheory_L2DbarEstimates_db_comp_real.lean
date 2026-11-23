-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.db_comp_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:37.800649+00:00
-- url     : https://prove2.me/submissions/1efd79de-c138-4cf6-ada4-281b46c9104a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
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
private theorem wd_wdb_ofReal_comp_real_chain (n : ℕ) (j : Fin n) (k : ℝ → ℝ) (hk : Differentiable ℝ k)
    (P : V n → ℝ) (w : V n) (hP : DifferentiableAt ℝ P w) :
    wd n j (fun y => ((k (P y) : ℝ) : ℂ)) w = ((deriv k (P w) : ℝ) : ℂ) * wd n j (fun y => ((P y : ℝ) : ℂ)) w ∧
    wdb n j (fun y => ((k (P y) : ℝ) : ℂ)) w = ((deriv k (P w) : ℝ) : ℂ) * wdb n j (fun y => ((P y : ℝ) : ℂ)) w := by
  have h1 : HasFDerivAt (fun y => ((P y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ P w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hP.hasFDerivAt
  have h2 : HasFDerivAt (fun y => ((k (P y) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (deriv k (P w) • fderiv ℝ P w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w ((hk (P w)).hasDerivAt.comp_hasFDerivAt w hP.hasFDerivAt)
  refine ⟨?_, ?_⟩ <;>
    simp only [wd, wdb, h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul] <;> ring
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (ph : M → ℝ) (hph : CkR n z 1 ph) (j : Fin n) (x : M) :
    db n z j (fun y => (k (ph y) : ℂ)) x = ((deriv k (ph x) : ℝ) : ℂ) * db n z j (fun y => (ph y : ℂ)) x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨he, ht, hsx⟩ := isChart_choose_and_symm_apply n z x h
    rw [db_eq_wdb_comp_chosen_chart_symm n z j _ x h, db_eq_wdb_comp_chosen_chart_symm n z j _ x h]
    have hP : DifferentiableAt ℝ (ph ∘ (Classical.choose h).symm) (z x) := by
      have h1 := ((Complex.reCLM.contDiff.comp_contDiffOn (hph _ he)).differentiableOn
        (by simp)).differentiableAt ((Classical.choose h).open_target.mem_nhds ht)
      exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp)
    refine (wd_wdb_ofReal_comp_real_chain n j k (hk.differentiable (by simp)) _ _ hP).2.trans ?_
    simp [hsx, Function.comp_def]
  · simp [d, db, h]
end ReciprocityTheory.L2DbarEstimates
