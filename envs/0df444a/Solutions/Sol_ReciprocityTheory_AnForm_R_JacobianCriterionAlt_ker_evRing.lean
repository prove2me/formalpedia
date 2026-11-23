-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.ker_evRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:50.109589+00:00
-- url     : https://prove2.me/submissions/162babbc-0594-4c36-8834-5c9a3a02c128

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_evRing_psi

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
    RingHom.ker (evRing K hK) = maximalIdeal (locR K p) := by
  have : (RingHom.ker (evRing K hK)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨psi p K (C c), by rw [evRing_psi, eval_C]⟩)
  exact IsLocalRing.eq_maximalIdeal this
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
