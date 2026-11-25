-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.isUnit_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:19.821807+00:00
-- url     : https://prove2.me/submissions/69c48d0f-4f51-4c76-b08e-1658e3ef255d

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
theorem _root_.solution {s : MvPolynomial (Fin n) ℂ} (hs : s ∉ ptI p) : IsUnit (psi p K s) :=
  (IsLocalization.map_units (localization₂ p) (⟨s, hs⟩ : (ptI p).primeCompl)).map (Ideal.Quotient.mk _)
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
