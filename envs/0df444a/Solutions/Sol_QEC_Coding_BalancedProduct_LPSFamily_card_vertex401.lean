-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSFamily.card_vertex401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:44:30.639965+00:00
-- url     : https://prove2.me/submissions/3e276e48-ee6f-4a83-8e15-15f83777fae5

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_pgl_two_zmod

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSFamily
open Matrix
open LPSGraph LPSTanner LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.LPSFamily
theorem _root_.solution
    (q : Nat) [Fact q.Prime] (hq40 : 40 < q) :
    Fintype.card (Vertex401 q) = q * (q ^ 2 - 1) :=
  card_pgl_two_zmod q hq40
end QEC.Coding.BalancedProduct.LPSFamily
