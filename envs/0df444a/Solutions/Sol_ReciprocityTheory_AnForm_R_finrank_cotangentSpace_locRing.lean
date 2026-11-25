-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.finrank_cotangentSpace_locRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:21.321618+00:00
-- url     : https://prove2.me/submissions/ba0af41e-12d4-494e-941d-c73aefb6ad9e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_finrank_cot_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsLocalRing (locRing K p)] :
    Module.finrank (IsLocalRing.ResidueField (locRing K p)) (IsLocalRing.CotangentSpace (locRing K p))
      + Module.finrank ℂ (jacSpan K p) = n := by
  exact @JacobianCriterionAlt.finrank_cot_eq n p K (inferInstanceAs (IsLocalRing (locRing K p)))
end ReciprocityTheory.AnForm.R
