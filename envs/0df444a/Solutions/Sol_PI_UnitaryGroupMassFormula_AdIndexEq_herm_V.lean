-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.herm_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:07.790882+00:00
-- url     : https://prove2.me/submissions/3b8d2c2a-c95d-4293-8217-293b320266ec

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_sigV_inclV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by
  funext i j
  have h : starRingEnd I.E (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  show sigV I v (inclV I v (I.J j i)) = inclV I v (I.J i j)
  rw [sigV_inclV]
  exact congrArg (inclV I v) h
end PI.UnitaryGroupMassFormula.AdIndexEq
