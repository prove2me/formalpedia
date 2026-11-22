-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15AcceptedLayer_dephased_eq_nextResource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:35:15.470715+00:00
-- url     : https://prove2.me/submissions/ffd22f4e-0513-4710-9a04-7b96bc237c50

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15AcceptedLayer_error_eq_iteration_succ
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisDephasing_mapDensity_eq_diagonalAResource
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    aBasisDephasing.mapDensity
        (bk15AcceptedLayer epsilon hpositive hthreshold rounds) =
      diagonalAResource
        (bk15IterationEpsilon epsilon hpositive hthreshold (rounds + 1)) := by
  apply aBasisDephasing_mapDensity_eq_diagonalAResource
  change bk15Iteration epsilon (rounds + 1) =
    aInputError (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
  change bk15Iteration epsilon (rounds + 1) =
    bk15OutputError (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
      aZeroDensity
  exact (bk15AcceptedLayer_error_eq_iteration_succ
    epsilon hpositive hthreshold rounds).symm
end QEC.Distillation.BK15.Threshold
