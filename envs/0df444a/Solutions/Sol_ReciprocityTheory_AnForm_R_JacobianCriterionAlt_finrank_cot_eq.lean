-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.JacobianCriterionAlt.finrank_cot_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:36.799821+00:00
-- url     : https://prove2.me/submissions/9d12ae53-7d69-47cc-966c-151696d5b168

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_finrank_cot_complex
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_finrank_residueField

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
    Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p))
      + Module.finrank ℂ (jacS K p) = n := by
  have h := finrank_cot_complex p K
  haveI : Module.Free ℂ (ResidueField (locR K p)) := Module.Free.of_divisionRing ℂ _
  haveI : Module.Free (ResidueField (locR K p)) (CotangentSpace (locR K p)) :=
    Module.Free.of_divisionRing (ResidueField (locR K p)) _
  rw [← Module.finrank_mul_finrank ℂ (ResidueField (locR K p)) (CotangentSpace (locR K p)),
    finrank_residueField, one_mul] at h
  exact h
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
