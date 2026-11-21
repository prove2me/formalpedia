-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TFidelityError_lt_threshold_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:22:48.743639+00:00
-- url     : https://prove2.me/submissions/f206d0e4-1a19-463e-822d-481c75ef534e

import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
namespace QEC.Distillation.BK05T
theorem _root_.solution
    (rho : DensityOperator QubitSpace) :
    bk05TFidelityError rho < bk05TThreshold <->
      bk05TFidelityThreshold < tFidelity rho := by
  have hfidelity := tFidelity_mem_Icc rho
  have hthresholdSquare : 0 <= (1 + Real.sqrt (3 / 7 : Real)) / 2 := by
    positivity
  unfold bk05TFidelityError bk05TFidelityThreshold
  rw [Real.sqrt_lt hthresholdSquare hfidelity.1]
  unfold bk05TThreshold
  constructor <;> intro h <;> nlinarith
end QEC.Distillation.BK05T
