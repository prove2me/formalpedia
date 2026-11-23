-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.sub_C_mem_span_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:16.528809+00:00
-- url     : https://prove2.me/submissions/bd8f9b46-fced-451f-9089-9d756b74b756

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Theorems.Thm_Bl_general_b_fact_left_more_goal1


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
    a - C (eval p a) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by
  first | exact Bl.general_b_fact_left_more.goal1 .. | (apply Bl.general_b_fact_left_more.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_more.goal1 <;> assumption)
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
