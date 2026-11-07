-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductTannerBridge.local_dual_check_row_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:14:37.264234+00:00
-- url     : https://prove2.me/submissions/4a438234-7e56-40ec-bee2-ab672ab17417

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_matrixRowCode_eq_dual_kernel
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
theorem _root_.solution (h : Matrix C A (ZMod 2))
    (g : Matrix C' A (ZMod 2))
    (hDual : parityCheckKernelCode (Matrix.toLin' g) =
      (parityCheckKernelCode (Matrix.toLin' h)).dual) :
    matrixRowCode h = parityCheckKernelCode (Matrix.toLin' g) ∧
      matrixRowCode g = parityCheckKernelCode (Matrix.toLin' h) := by
  constructor
  · rw [matrixRowCode_eq_dual_kernel, hDual]
  · rw [matrixRowCode_eq_dual_kernel, hDual, LinearCode.dual_dual_eq]
end QEC.Coding.QuantumTanner.LiftedProductTannerBridge
