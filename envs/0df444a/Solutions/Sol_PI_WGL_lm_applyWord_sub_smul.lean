-- Prove2me | solution 1 for PI.WGL.lm_applyWord_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:40.380923+00:00
-- url     : https://prove2.me/submissions/aa05d049-5e33-4eb0-a5fe-b5e188d2e5aa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
import Theorems.Thm_PI_WGL_lm_rowDiv_sub
import Theorems.Thm_PI_WGL_lm_rowDiv_smul

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
theorem _root_.solution {R : Type*} [CommRing R] {r m : ℕ} (w : List (Fin r × Fin r × ℕ)) (c : R)
    (f g : MvPolynomial (Fin r × Fin m) R) :
    applyWord R w (f - c • g) = applyWord R w f - c • applyWord R w g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (f - c • g)) =
      rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) - c • rowDiv R x.1 x.2.1 x.2.2 (applyWord R w g)
    rw [ih, lm_rowDiv_sub, lm_rowDiv_smul]
end PI.WGL
