-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:39.506382+00:00
-- url     : https://prove2.me/submissions/461ffa87-3446-4f54-a9a1-95e9fafa0858

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
theorem _root_.solution (p : Fin n → ℂ) (i : Fin n) : gradP p (X i - C (p i)) = Pi.single i 1 := by
  ext j; simp [gradP, pderiv_X, Pi.single_apply, eq_comm]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
