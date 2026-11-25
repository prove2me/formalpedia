-- Prove2me | solution 1 for PI.WGL.equivariant_last_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:13.656181+00:00
-- url     : https://prove2.me/submissions/446ffedc-aa49-45bc-8a0d-93585720a67b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_PI_WGL_EqvWt_weight_lastW
import Theorems.Thm_PI_WGL_EqvWt_equivariant_last_degree_coeff

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
open EqvWt
namespace PI.WGL
theorem _root_.solution : EqvLast := by
  intro n N h lam mu _ φ hφ s hs
  subst h
  intro m hm
  rw [weight_lastW]
  have := equivariant_last_degree_coeff lam mu φ hφ s hs m hm
  show rowDeg m (Fin.last n) = (wsum lam - wsum mu - lam.detShift).toNat
  omega
end PI.WGL
