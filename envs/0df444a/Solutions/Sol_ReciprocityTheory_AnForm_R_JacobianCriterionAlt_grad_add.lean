-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:14.234442+00:00
-- url     : https://prove2.me/submissions/22c1fff2-3235-4786-a837-9af12e0b86e3

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA

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
theorem _root_.solution (p : Fin n → ℂ) (x y : MvPolynomial (Fin n) ℂ) :
    gradP p (x + y) = gradP p x + gradP p y := by
  ext j; simp [gradP]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
