-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.exists_mul_mem_of_algebraMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:38.943779+00:00
-- url     : https://prove2.me/submissions/47aedfde-dd98-451e-a4ce-011d94758b41

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
theorem _root_.solution (p : Fin n → ℂ) {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {a : MvPolynomial (Fin n) ℂ}
    (h : algebraMap _ (localization₂ p) a ∈ I.map (algebraMap _ (localization₂ p))) :
    ∃ s, s ∉ ptI p ∧ s * a ∈ I := by
  obtain ⟨⟨x, s⟩, hx⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (ptI p).primeCompl (localization₂ p)).mp h
  rw [← map_mul] at hx
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (ptI p).primeCompl (localization₂ p)).mp hx
  refine ⟨c * s, (ptI p).primeCompl.mul_mem c.2 s.2, ?_⟩
  have : (c : MvPolynomial (Fin n) ℂ) * s * a = c * x := by rw [← hc]; ring
  rw [this]; exact I.mul_mem_left _ x.2
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
