-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15HInputError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:29:08.491224+00:00
-- url     : https://prove2.me/submissions/c932faed-1977-4ba9-8fb6-9d12ce0fb9a2

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hFidelity_mem_Icc


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
theorem _root_.solution (rho : DensityOperator QubitSpace) :
    0 <= bk15HInputError rho := by
  have hfidelity := hFidelity_mem_Icc rho
  unfold bk15HInputError
  have hfactor : 0 <= hFidelity rho * (1 - hFidelity rho) :=
    mul_nonneg hfidelity.1 (sub_nonneg.mpr hfidelity.2)
  nlinarith
end QEC.Distillation.BK15.Threshold
