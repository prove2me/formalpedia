-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.bk15_r_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:17:00.533117+00:00
-- url     : https://prove2.me/submissions/2ee70630-25b8-46db-a779-6554f422a920

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
namespace QEC.Distillation.BK15.Recurrence
theorem _root_.solution (epsilon : BK15Epsilon) : 0 ≤ bk15_r epsilon := by
  unfold bk15_r
  linarith [epsilon.le_half]
end QEC.Distillation.BK15.Recurrence
