-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15RawZeroEndpoint_is_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:32:05.386967+00:00
-- url     : https://prove2.me/submissions/97813d6d-7d5f-457d-bcfd-9065e4f5a6b1

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Protocol_decodedOperation_zeroEpsilon


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
theorem _root_.solution :
    decodedOperation.mapDensity (rawInput zeroEpsilon) = aZeroDensity := by
  exact decodedOperation_zeroEpsilon
end QEC.Distillation.BK15.Threshold
