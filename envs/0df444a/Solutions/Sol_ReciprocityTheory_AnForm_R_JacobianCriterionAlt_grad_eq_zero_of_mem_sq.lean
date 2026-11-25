-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_eq_zero_of_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:14.849171+00:00
-- url     : https://prove2.me/submissions/c74be915-9d27-406d-9014-87a52b7a7675

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_add
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_grad_mul

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
theorem _root_.solution (p : Fin n → ℂ) {q : MvPolynomial (Fin n) ℂ}
    (hq : q ∈ ptI p ^ 2) : gradP p q = 0 := by
  rw [pow_two] at hq
  refine Submodule.mul_induction_on hq ?_ ?_
  · intro x hx y hy
    rw [grad_mul, mem_ptIdeal.mp hx, mem_ptIdeal.mp hy]; simp
  · intro x y hx hy; rw [grad_add, hx, hy, add_zero]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
