-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_recursive_handoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:31:49.563414+00:00
-- url     : https://prove2.me/submissions/9f47c2ea-406a-4fd1-837f-220365bccfab

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar)
    (depth : Nat) (site : Fin 15) :
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 2)) site =
      aBasisDephasing.mapDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1))) := by
  rfl
end QEC.Distillation.BK15.Threshold
