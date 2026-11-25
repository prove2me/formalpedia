-- Prove2me | solution 1 for PI.WGL.lm_map_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:13.081366+00:00
-- url     : https://prove2.me/submissions/291b8f14-8a92-4998-aeca-5c8eeecc2fef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
import Theorems.Thm_Formalism_UG_P_wlocal_map_hw


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
theorem _root_.solution {n : ℕ} (sg : DomWeight n) :
    map (Int.castRingHom ℂ) (extremal ℤ n sg) = extremal ℂ n sg := by
  unfold extremal
  exact Formalism.UG.P.wlocal_map_hw _ _ _
end PI.WGL
