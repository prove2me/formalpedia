-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.finrank_cot_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:05.398798+00:00
-- url     : https://prove2.me/submissions/33729a81-1c34-4e94-894c-ff1524e056d6

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_ker_Phi
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_Phi_surjective

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
variable {n : ℕ} (p : Fin n → ℂ) (K : Ideal (MvPolynomial (Fin n) ℂ)) [IsLocalRing (locR K p)]
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
theorem _root_.solution :
    Module.finrank ℂ (CotangentSpace (locR K p)) + Module.finrank ℂ (jacS K p) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (Phi p K)
  rw [LinearMap.range_eq_top.mpr (Phi_surjective p K), finrank_top, ker_Phi, Module.finrank_fin_fun] at h
  exact h
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
