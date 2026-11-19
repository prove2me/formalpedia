-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.bk15_recurrence_denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:19:15.274736+00:00
-- url     : https://prove2.me/submissions/34983794-f44c-4589-898b-e65b66deb07a

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15_r_nonneg

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
theorem _root_.solution (epsilon : BK15Epsilon) :
    0 < 1 + 15 * bk15_r epsilon ^ 8 := by
  have hpow : 0 ≤ bk15_r epsilon ^ 8 :=
    pow_nonneg (bk15_r_nonneg epsilon) _
  nlinarith
end QEC.Distillation.BK15.Recurrence
