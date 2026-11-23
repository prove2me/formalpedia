-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.evRing_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:11.991402+00:00
-- url     : https://prove2.me/submissions/d63618b4-e0dd-4f89-bff5-a4c58eb09062

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
variable {p : Fin n → ℂ} (K : Ideal (MvPolynomial (Fin n) ℂ))
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
theorem _root_.solution (hK : K ≤ ptI p) (a : MvPolynomial (Fin n) ℂ) :
    evRing K hK (psi p K a) = eval p a := by
  rw [evRing, psi, RingHom.comp_apply, Ideal.Quotient.lift_mk, evLoc_algebraMap]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
