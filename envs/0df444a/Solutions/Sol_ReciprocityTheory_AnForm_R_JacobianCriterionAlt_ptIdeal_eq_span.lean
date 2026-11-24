-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ptIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:34.329864+00:00
-- url     : https://prove2.me/submissions/66d44ad7-a6b1-4cc1-bc8e-fe68b2e10e63

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
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
theorem _root_.solution (p : Fin n → ℂ) :
    ptI p = Ideal.span (Set.range fun i => X i - C (p i)) := by
  apply le_antisymm
  · intro a ha
    have := sub_C_mem_span_lin p a
    rwa [mem_ptIdeal.mp ha, map_zero, sub_zero] at this
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [mem_ptIdeal]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
