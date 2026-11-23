-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.grad_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:39.749556+00:00
-- url     : https://prove2.me/submissions/3438ac3c-8574-4e27-9ff0-243efc411c21

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
theorem _root_.solution (p : Fin n → ℂ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℂ) :
    gradP p (∑ i ∈ s, f i) = ∑ i ∈ s, gradP p (f i) := by
  ext j; simp [gradP, map_sum]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
