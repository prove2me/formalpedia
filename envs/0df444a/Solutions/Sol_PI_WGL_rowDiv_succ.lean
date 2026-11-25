-- Prove2me | solution 1 for PI.WGL.rowDiv_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:00:31.471825+00:00
-- url     : https://prove2.me/submissions/5a62664b-8603-49a5-878b-c1e0bfb38395

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Theorems.Thm_PI_WGL_deriv_rowGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b (k + 1) f * ((k : MvPolynomial (Fin r × Fin m) R) + 1) +
      (if a = b then rowDiv R a b k f * (k : MvPolynomial (Fin r × Fin m) R) else 0) =
      rowDiv R a b k (pol R a b f) := by
  have h := congrArg (fun p => Polynomial.coeff p k) (deriv_rowGen R a b f)
  unfold rowDiv
  rw [← h]
  by_cases hab : a = b
  · simp only [hab, if_true, add_mul, one_mul, Polynomial.coeff_add]
    rw [Polynomial.coeff_derivative]
    cases k with
    | zero => simp [Polynomial.coeff_derivative]
    | succ k =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      push_cast; ring
  · simp only [hab, if_false, one_mul, add_zero, Polynomial.coeff_derivative]
end PI.WGL
