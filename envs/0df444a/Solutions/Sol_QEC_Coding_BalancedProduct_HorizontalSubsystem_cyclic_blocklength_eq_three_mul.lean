-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.HorizontalSubsystem.cyclic_blocklength_eq_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:07.733202+00:00
-- url     : https://prove2.me/submissions/96f5ddb7-64d0-4229-8483-2831c1441406

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_card_qubitIndex
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v
namespace QEC.Coding.BalancedProduct.HorizontalSubsystem
theorem _root_.solution
    {aRow aCol : Type} [Fintype aRow] [Fintype aCol]
    (q edgeCount : Nat) [NeZero q]
    (hHorizontal : q * Fintype.card aCol = edgeCount)
    (hLocalChecks : q * Fintype.card aRow = 2 * edgeCount) :
    Fintype.card
        (LiftedProduct.QubitIndex aRow aCol Unit Unit (CyclicGroup q)) =
      3 * edgeCount := by
  rw [Cyclic.card_qubitIndex, Nat.mul_add, hHorizontal, hLocalChecks]
  omega
end QEC.Coding.BalancedProduct.HorizontalSubsystem
