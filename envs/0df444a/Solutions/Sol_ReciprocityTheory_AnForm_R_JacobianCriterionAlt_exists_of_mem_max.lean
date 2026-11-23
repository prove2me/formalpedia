-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.exists_of_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:39.17758+00:00
-- url     : https://prove2.me/submissions/b5e8d155-524f-4863-8e37-022a33ca6b75

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_psi_mem_max_iff

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
theorem _root_.solution [IsLocalRing (locR K p)] (hK : K ≤ ptI p) {m : locR K p}
    (hm : m ∈ maximalIdeal (locR K p)) :
    ∃ a s, a ∈ ptI p ∧ s ∉ ptI p ∧ m * psi p K s = psi p K a := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj (ptI p).primeCompl x
  have h : Ideal.Quotient.mk _ x * psi p K s = psi p K a := by
    simp only [psi, RingHom.coe_comp, Function.comp_apply, ← hx, map_mul]
  refine ⟨a, s, ?_, s.2, h⟩
  rw [← psi_mem_max_iff K hK, ← h]
  exact Ideal.mul_mem_right _ _ hm
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
