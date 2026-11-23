-- Prove2me | solution 1 for PI.WGL.EqvWt.two_zpow_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:20.724239+00:00
-- url     : https://prove2.me/submissions/13ec4252-72e1-4d62-aa4c-0589beeab7ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt

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
open PI.WGL.EqvWt
namespace PI.WGL.EqvWt
theorem _root_.solution {k l : ℤ} (e : (2 : ℂ) ^ k = (2 : ℂ) ^ l) : k = l := by
  have h : (((2 : ℝ) ^ k : ℝ) : ℂ) = (((2 : ℝ) ^ l : ℝ) : ℂ) := by
    push_cast
    exact e
  exact zpow_right_injective₀ (by norm_num) (by norm_num) (Complex.ofReal_injective h)
end PI.WGL.EqvWt
