-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSFamily.card_edgeOrbit401_sub_checkOrbit401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:49:35.878325+00:00
-- url     : https://prove2.me/submissions/58f69744-f8aa-4f05-bb84-3644bbec160b

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_edgeOrbit401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_card_checkOrbit401

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
    Fintype.card (EdgeOrbit401 q hq) -
        Fintype.card (CheckOrbit401 q) = q ^ 2 - 1 := by
  rw [card_edgeOrbit401 q hq40 hq, card_checkOrbit401 q hq40]
  omega
end QEC.Coding.BalancedProduct.LPSFamily
