-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSFamily.card_edgeOrbit401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:47:05.996385+00:00
-- url     : https://prove2.me/submissions/a22a760c-e657-4029-a50e-136cea1aea6f

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_vertex401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_card_edge401_eq_cyclic_mul_edgeOrbit
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_edge401_eq


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
    Fintype.card (EdgeOrbit401 q hq) = 201 * (q ^ 2 - 1) := by
  have hqpos : 0 < q := by omega
  apply Nat.eq_of_mul_eq_mul_left hqpos
  calc
    q * Fintype.card (EdgeOrbit401 q hq) =
        Fintype.card (Edge401 q hq) :=
      (card_edge401_eq_cyclic_mul_edgeOrbit q hq).symm
    _ = 201 * Fintype.card (Vertex401 q) :=
      LPSTannerExpansion.card_edge401_eq q hq40 hq
    _ = q * (201 * (q ^ 2 - 1)) := by
      rw [card_vertex401 q hq40]
      ring
end QEC.Coding.BalancedProduct.LPSFamily
