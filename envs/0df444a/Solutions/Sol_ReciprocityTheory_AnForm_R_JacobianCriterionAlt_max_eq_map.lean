-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.max_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:56.196335+00:00
-- url     : https://prove2.me/submissions/25d5580c-92f4-49c2-a487-74836c950fb6

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_isUnit_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_psi_mem_max_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_of_mem_max

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
theorem _root_.solution [IsLocalRing (locR K p)] (hK : K ≤ ptI p) :
    maximalIdeal (locR K p) = (ptI p).map (psi p K) := by
  apply le_antisymm
  · intro m hm
    obtain ⟨a, s, ha, hs, h⟩ := exists_of_mem_max K hK hm
    have hu := isUnit_psi K hs
    have : m = psi p K a * ↑hu.unit⁻¹ := by
      rw [← h, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (psi_mem_max_iff K hK a).mpr ha
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
