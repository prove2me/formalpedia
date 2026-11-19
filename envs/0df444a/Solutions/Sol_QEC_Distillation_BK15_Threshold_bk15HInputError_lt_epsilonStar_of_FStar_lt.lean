-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15HInputError_lt_epsilonStar_of_FStar_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:31:03.619897+00:00
-- url     : https://prove2.me/submissions/7d1fe957-d1f1-4193-a9c5-726532212c41

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_FStar_sq
import Theorems.Thm_QEC_Distillation_BK15_Threshold_FStar_nonneg
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
theorem _root_.solution
    (rho : DensityOperator QubitSpace) (hfidelity : FStar < hFidelity rho) :
    bk15HInputError rho < epsilonStar := by
  have hfid := hFidelity_mem_Icc rho
  have hsquare : FStar ^ 2 < hFidelity rho ^ 2 :=
    (sq_lt_sq₀ FStar_nonneg hfid.1).mpr hfidelity
  rw [FStar_sq] at hsquare
  unfold bk15HInputError
  linarith
end QEC.Distillation.BK15.Threshold
