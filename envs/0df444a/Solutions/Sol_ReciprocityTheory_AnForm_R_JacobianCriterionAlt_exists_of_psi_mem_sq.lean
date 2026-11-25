-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.exists_of_psi_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:22:36.618324+00:00
-- url     : https://prove2.me/submissions/81e3d4a6-2c48-4fbd-950b-55a6178784bf

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_mul_mem_of_algebraMap_mem
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_max_eq_map

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
theorem _root_.solution [IsLocalRing (locR K p)] (hK : K ≤ ptI p)
    {l : MvPolynomial (Fin n) ℂ} (hl : psi p K l ∈ maximalIdeal (locR K p) ^ 2) :
    ∃ s, s ∉ ptI p ∧ s * l ∈ ptI p ^ 2 ⊔ K := by
  rw [max_eq_map K hK, ← Ideal.map_pow, psi, ← Ideal.map_map] at hl
  change Ideal.Quotient.mk _ (algebraMap _ (localization₂ p) l) ∈ _ at hl
  rw [Ideal.mem_quotient_iff_mem_sup, ← Ideal.map_sup] at hl
  exact exists_mul_mem_of_algebraMap_mem p hl
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
