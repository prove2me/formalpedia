-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.le_ptIdeal_of_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:09.453169+00:00
-- url     : https://prove2.me/submissions/f7b5b0a1-dd1c-4216-b70f-adcdf8b9199c

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
theorem _root_.solution [Nontrivial (locR K p)] : K ≤ ptI p := by
  intro k hk
  by_contra hkp
  have hu : IsUnit (algebraMap _ (localization₂ p) k) :=
    IsLocalization.map_units (localization₂ p) (⟨k, hkp⟩ : (ptI p).primeCompl)
  have htop := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (algebraMap _ (localization₂ p)) hk) hu
  have : (1 : locR K p) = 0 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, htop]
    exact Submodule.mem_top
  exact one_ne_zero this
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
