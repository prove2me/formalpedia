-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BridgeInvAlg.theta_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:19.152729+00:00
-- url     : https://prove2.me/submissions/6728ee85-b88f-4224-a603-11571910e4a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_InvAlgOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BridgeInvAlg
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
namespace PI.UnitaryGroupMassFormula.BridgeInvAlg
theorem _root_.solution (I : AutInst) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    Theta I x = (fun v => thetaV I v x, tauF I x) := rfl
end PI.UnitaryGroupMassFormula.BridgeInvAlg
