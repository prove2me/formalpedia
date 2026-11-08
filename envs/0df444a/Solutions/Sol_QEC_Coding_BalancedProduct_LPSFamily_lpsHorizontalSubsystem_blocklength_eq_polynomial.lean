-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSFamily.lpsHorizontalSubsystem_blocklength_eq_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:49:49.481579+00:00
-- url     : https://prove2.me/submissions/2331949d-c2d6-4552-a912-bac7a573209a

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_vertex401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_blocklength_eq


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSFamily
open Matrix
open LPSGraph LPSTanner LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.LPSFamily
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card
        (LiftedProduct.QubitIndex
          (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit
          (Cyclic.CyclicGroup q)) =
      401 * q * (q ^ 2 - 1) := by
  rw [lpsHorizontalSubsystem_blocklength_eq q hq40 hq,
    card_vertex401 q hq40]
  ring
end QEC.Coding.BalancedProduct.LPSFamily
