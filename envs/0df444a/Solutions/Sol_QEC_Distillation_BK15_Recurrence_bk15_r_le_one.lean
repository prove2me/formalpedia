-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.bk15_r_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:17:10.648765+00:00
-- url     : https://prove2.me/submissions/038935f3-3875-4490-a97e-b87f686fd53b

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
theorem _root_.solution (epsilon : BK15Epsilon) : bk15_r epsilon ≤ 1 := by
  unfold bk15_r
  linarith [epsilon.nonneg]
end QEC.Distillation.BK15.Recurrence
