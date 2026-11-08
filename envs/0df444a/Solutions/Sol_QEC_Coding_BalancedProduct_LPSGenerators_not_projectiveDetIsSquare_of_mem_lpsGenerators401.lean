-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.not_projectiveDetIsSquare_of_mem_lpsGenerators401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:55:29.972194+00:00
-- url     : https://prove2.me/submissions/259ba0df-f168-4fd5-9449-45469afd11ae

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_not_projectiveDetIsSquare_lpsGenerator401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_mem_lpsGenerators401_iff

set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
namespace QEC.Coding.BalancedProduct.LPSGenerators
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {s : PGL(2, ZMod q)}
    (hs : s ∈ lpsGenerators401 q hq) :
    ¬ ProjectiveDetIsSquare s := by
  rcases (mem_lpsGenerators401_iff q hq s).mp hs with ⟨t, ht, rfl⟩
  exact not_projectiveDetIsSquare_lpsGenerator401 q hq t ht
end QEC.Coding.BalancedProduct.LPSGenerators
