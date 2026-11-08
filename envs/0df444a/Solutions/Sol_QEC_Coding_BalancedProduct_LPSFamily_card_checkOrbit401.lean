-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSFamily.card_checkOrbit401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:47:07.790588+00:00
-- url     : https://prove2.me/submissions/27dea6d8-597f-4ce5-91f1-1297f4f06140

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_vertex401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_check401_eq_cyclic_mul_checkOrbit
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_check401_eq


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSFamily
open Matrix
open LPSGraph LPSTanner LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.LPSFamily
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) :
    Fintype.card (CheckOrbit401 q) = 200 * (q ^ 2 - 1) := by
  have hqpos : 0 < q := by omega
  apply Nat.eq_of_mul_eq_mul_left hqpos
  calc
    q * Fintype.card (CheckOrbit401 q) =
        Fintype.card (Check401 q) :=
      (card_check401_eq_cyclic_mul_checkOrbit q).symm
    _ = 200 * Fintype.card (Vertex401 q) :=
      LPSTannerExpansion.card_check401_eq q
    _ = q * (200 * (q ^ 2 - 1)) := by
      rw [card_vertex401 q hq40]
      ring
end QEC.Coding.BalancedProduct.LPSFamily
