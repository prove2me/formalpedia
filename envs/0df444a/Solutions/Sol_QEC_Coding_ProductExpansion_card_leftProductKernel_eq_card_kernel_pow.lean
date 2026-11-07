-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_leftProductKernel_eq_card_kernel_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:50.884019+00:00
-- url     : https://prove2.me/submissions/18061d7f-6f2e-4fae-9a54-c2c80d6e3cb5

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq F] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (M : Matrix R' W F) :
    Nat.card {h : Matrix R W F // M * h.transpose = 0} =
      (Nat.card (LinearMap.ker M.mulVecLin)) ^ Nat.card R := by
  classical
  rw [Nat.card_congr (leftProductKernelEquivRows (R := R) M)]
  exact Nat.card_fun
end QEC.Coding.ProductExpansion
