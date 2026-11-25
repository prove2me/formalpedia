-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.db_expNeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:54.59061+00:00
-- url     : https://prove2.me/submissions/ae2f478f-4b55-4f13-aa1f-40ed20468307

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
private theorem differentiableAt_comp_chart_symm_of_ck_one {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) : DifferentiableAt ℝ (f ∘ e.symm) (z x) := by
  rw [he hx]
  exact ((hf e he).differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))
end
end ReciprocityTheory.L2DbarEstimates.E
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : CkR n z 1 ph) (j : Fin n)
    (x : M) :
    db n z j (fun y => (Real.exp (-ph y) : ℂ)) x =
      -((Real.exp (-ph x) : ℂ) * db n z j (fun y => (ph y : ℂ)) x) := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos h]
    obtain ⟨he, hx⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx
    have hex : e.symm (z x) = x := by
      rw [hzx]
      exact e.left_inv hx
    have hP := differentiableAt_comp_chart_symm_of_ck_one n z (fun y => (ph y : ℂ)) hph e he x hx
    have hQ : DifferentiableAt ℝ (fun w => ph (e.symm w)) (z x) := by
      have := Complex.reCLM.differentiableAt.comp (z x) hP
      simpa [Function.comp_def] using this
    have h1 : fderiv ℝ ((fun y => (Real.exp (-ph y) : ℂ)) ∘ e.symm) (z x) =
        Complex.ofRealCLM.comp (Real.exp (-ph (e.symm (z x))) •
          -(fderiv ℝ (fun w => ph (e.symm w)) (z x))) :=
      (Complex.ofRealCLM.hasFDerivAt.comp (z x) hQ.hasFDerivAt.neg.exp).fderiv
    have h2 : fderiv ℝ ((fun y => (ph y : ℂ)) ∘ e.symm) (z x) =
        Complex.ofRealCLM.comp (fderiv ℝ (fun w => ph (e.symm w)) (z x)) :=
      (Complex.ofRealCLM.hasFDerivAt.comp (z x) hQ.hasFDerivAt).fderiv
    simp only [wdb]
    rw [h1, h2]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, Complex.ofRealCLM_apply, smul_eq_mul, hex]
    push_cast
    ring
  · simp [db, dif_neg h]
end ReciprocityTheory.L2DbarEstimates.E
