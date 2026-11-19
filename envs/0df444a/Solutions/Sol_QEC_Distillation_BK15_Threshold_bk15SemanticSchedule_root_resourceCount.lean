-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15SemanticSchedule_root_resourceCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:29:41.138214+00:00
-- url     : https://prove2.me/submissions/b6072973-8b56-4797-838b-c30921e3ff33

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_resourceCount



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
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    (bk15Run
      (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
      (bk15Iteration_pos_and_lt_epsilonStar
        (bk15HInputError rho) hpositive hthreshold depth).1).resourceCount = 15 := by
  exact bk15Run_resourceCount _ _
end QEC.Distillation.BK15.Threshold
