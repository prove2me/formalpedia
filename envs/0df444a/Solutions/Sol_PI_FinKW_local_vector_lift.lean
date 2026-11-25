-- Prove2me | solution 1 for PI.FinKW.local_vector_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:07:13.83114+00:00
-- url     : https://prove2.me/submissions/8a331488-f3b7-4fee-994a-d8c78108e2b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
import Theorems.Thm_PI_FinKW_psiV_liftOne_same
import Theorems.Thm_PI_FinKW_psiV_liftOne_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW
theorem _root_.solution : LiftV := by
  intro I v y
  refine ⟨fun i => liftOne I v (y i), ?_, ?_⟩
  · funext i
    exact psiV_liftOne_same I v (y i)
  · intro w hw
    funext i
    exact psiV_liftOne_ne I hw (y i)
end PI.FinKW
