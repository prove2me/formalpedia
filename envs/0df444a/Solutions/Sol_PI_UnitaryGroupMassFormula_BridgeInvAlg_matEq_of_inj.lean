-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BridgeInvAlg.matEq_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:41.112219+00:00
-- url     : https://prove2.me/submissions/ba89579f-4056-4a94-b8ed-6864a3136451

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_BridgeHomFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantAlgebraComparison_MapThetaEq
import Theorems.Thm_PI_UnitaryGroupMassFormula_BridgeInvAlg_theta_apply


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
theorem _root_.solution (hi : ThetaInj) (I : AutInst)
    {A B : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E)}
    (hv : ∀ v, A.map (thetaV I v) = B.map (thetaV I v)) (hf : A.map (tauF I) = B.map (tauF I)) :
    A = B := by
  ext i j
  apply hi I
  rw [theta_apply, theta_apply]
  refine Prod.ext (funext fun v => ?_) ?_
  · exact congrArg (fun M => M i j) (hv v)
  · exact congrArg (fun M => M i j) hf
end PI.UnitaryGroupMassFormula.BridgeInvAlg
