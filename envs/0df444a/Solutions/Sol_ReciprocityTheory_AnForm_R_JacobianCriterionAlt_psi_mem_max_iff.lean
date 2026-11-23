-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.psi_mem_max_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:01:52.997162+00:00
-- url     : https://prove2.me/submissions/c30b86e5-afd7-4aa0-b0b2-9bfcaa5d1a81

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_evRing_psi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_ker_evRing

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
    (a : MvPolynomial (Fin n) ℂ) : psi p K a ∈ maximalIdeal (locR K p) ↔ a ∈ ptI p := by
  rw [← ker_evRing K hK, RingHom.mem_ker, evRing_psi, mem_ptIdeal]
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
