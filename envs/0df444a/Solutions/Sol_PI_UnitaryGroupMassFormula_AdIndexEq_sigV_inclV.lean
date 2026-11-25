-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.sigV_inclV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:30.051495+00:00
-- url     : https://prove2.me/submissions/75b4bb02-d621-4ba3-8ae8-01c22fcdb139

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_sigV_tmul

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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    sigV I v (inclV I v e) = inclV I v (star e) := by
  exact sigV_tmul I v 1 e
end PI.UnitaryGroupMassFormula.AdIndexEq
