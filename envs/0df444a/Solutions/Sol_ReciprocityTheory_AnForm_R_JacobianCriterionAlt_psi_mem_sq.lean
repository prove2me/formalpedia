-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.psi_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:43.817802+00:00
-- url     : https://prove2.me/submissions/d27fe559-0a3d-441e-8846-56bffaa713c4

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
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
theorem _root_.solution [IsLocalRing (locR K p)] (hK : K ≤ ptI p) {a : MvPolynomial (Fin n) ℂ}
    (ha : a ∈ ptI p ^ 2) : psi p K a ∈ maximalIdeal (locR K p) ^ 2 := by
  rw [max_eq_map K hK, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
