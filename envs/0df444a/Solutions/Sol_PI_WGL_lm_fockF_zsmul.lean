-- Prove2me | solution 1 for PI.WGL.lm_fockF_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:56.890344+00:00
-- url     : https://prove2.me/submissions/20948108-1f47-43b8-b4e4-a9e2a40d8f1e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
import Theorems.Thm_PI_WGL_lm_fockF_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution {σ : Type*} (a : ℤ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (a • f) g = a * Formalism.REAL.fockF f g := by
  rw [← Int.cast_smul_eq_zsmul ℂ, lm_fockF_smul]
end PI.WGL
