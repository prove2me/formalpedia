-- Prove2me | solution 1 for PI.WGL.deriv_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:42:22.820856+00:00
-- url     : https://prove2.me/submissions/76e2ac59-e835-4703-a747-34ecd25d1419

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
import Theorems.Thm_PI_WGL_pol_mul
import Theorems.Thm_PI_WGL_pol_X
import Theorems.Thm_PI_WGL_pol_C
import Theorems.Thm_P2M_PI_WGL_rowGen_X__44b3555ab4d3
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
theorem _root_.solution (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b f) =
      rowGen R a b (pol R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [pol_C, map_zero]
    have : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [this, Polynomial.derivative_C, mul_zero]
  | add p q hp hq => rw [map_add, Polynomial.derivative_add, mul_add, hp, hq, map_add, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, mul_add, pol_mul, map_add, map_mul, map_mul, ← hp, pol_X]
    have hg : (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b (X v)) =
        rowGen R a b (if v.1 = b then X (a, v.2) else 0) := by
      rw [rowGen_X']
      by_cases hv : v.1 = b
      · simp only [hv, if_true, Polynomial.derivative_add, Polynomial.derivative_C, zero_add,
          Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, mul_zero, add_zero, rowGen_X']
        by_cases hab : a = b
        · simp [hab]; ring
        · simp [hab]
      · simp [hv]
    rw [← hg]; ring
end PI.WGL
