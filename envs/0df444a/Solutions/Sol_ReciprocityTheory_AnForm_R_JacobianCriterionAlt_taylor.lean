-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.taylor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:52.780798+00:00
-- url     : https://prove2.me/submissions/2d5e8419-4f97-4f91-895d-ad4fc8d81e0d

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_add
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_mul
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_C
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_sum
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_lin
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_sub_C_mem_span_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
theorem _root_.solution (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    a - C (eval p a) - ∑ i, C (gradP p a i) * (X i - C (p i)) ∈ ptI p ^ 2 := by
  obtain ⟨b, hb⟩ := (Ideal.mem_span_range_iff_exists_fun).mp (sub_C_mem_span_lin p a)
  have ha : a = C (eval p a) + ∑ i, b i * (X i - C (p i)) := by rw [hb]; ring
  have hg : ∀ j, gradP p a j = eval p (b j) := by
    intro j
    have h1 := congrArg (fun f => gradP p f j) ha
    simp only [grad_add, grad_C, grad_sum, grad_mul, grad_lin] at h1
    simpa [Pi.single_apply] using h1
  have : a - C (eval p a) - ∑ i, C (gradP p a i) * (X i - C (p i)) =
      ∑ i, (b i - C (eval p (b i))) * (X i - C (p i)) := by
    rw [← hb]; simp only [hg, sub_mul, Finset.sum_sub_distrib]
  rw [this, pow_two]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul ?_ ?_
  · simp [mem_ptIdeal]
  · simp [mem_ptIdeal]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
