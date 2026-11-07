-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductTannerBridge.matrixRowCode_eq_dual_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:09:44.910739+00:00
-- url     : https://prove2.me/submissions/092acd6e-69bb-4c5e-b332-2a03e6b0f36f

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
import Theorems.Thm_QEC_Coding_LinearCode_dual_dual_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTannerBridge
open Classical
open LiftedProductRestriction LiftedProductActionBridge LiftedProductTensorBridge
universe v
variable {G A B C D C' D' : Type v} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']
namespace QEC.Coding.QuantumTanner.LiftedProductTannerBridge
theorem _root_.solution (P : Matrix C A (ZMod 2)) :
    matrixRowCode P = (parityCheckKernelCode (Matrix.toLin' P)).dual := by
  rw [← parityCheckRowCode_dual_eq_kernelCode, LinearCode.dual_dual_eq]
  rfl
end QEC.Coding.QuantumTanner.LiftedProductTannerBridge
