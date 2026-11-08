-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.card_lpsGenerators401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:21:07.880631+00:00
-- url     : https://prove2.me/submissions/8c61d52b-484d-40ca-b54e-4e62b712eeb7

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_card_shell401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGenerator401_injective

set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
namespace QEC.Coding.BalancedProduct.LPSGenerators
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    (lpsGenerators401 q hq).card = 402 := by
  classical
  rw [lpsGenerators401,
    Finset.card_image_of_injective _ (lpsGenerator401_injective q hq40 hq)]
  simpa using card_shell401
end QEC.Coding.BalancedProduct.LPSGenerators
