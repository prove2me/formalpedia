-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSFamily.lt_admissiblePrime401At
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:55:16.310809+00:00
-- url     : https://prove2.me/submissions/2f5bd955-d296-4544-9491-f4209fc46c8b

import Definitions.Def_QEC_Coding_BalancedProduct_LPSQuotientTanner
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSFamily
open Matrix
open LPSGraph LPSTanner LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.LPSFamily
theorem _root_.solution (B : Nat) :
    B < (admissiblePrime401At B).q :=
  Classical.choose_spec (exists_admissiblePrime401_gt B)
end QEC.Coding.BalancedProduct.LPSFamily
