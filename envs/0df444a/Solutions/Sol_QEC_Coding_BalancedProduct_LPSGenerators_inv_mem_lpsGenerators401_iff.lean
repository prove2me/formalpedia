-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.inv_mem_lpsGenerators401_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:02:11.25187+00:00
-- url     : https://prove2.me/submissions/befa0346-91f2-4c8c-84f4-05ccc1aa000b

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_inv_mem_lpsGenerators401_of_mem

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
    (s : PGL(2, ZMod q)) :
    s⁻¹ ∈ lpsGenerators401 q hq ↔ s ∈ lpsGenerators401 q hq := by
  constructor
  · intro hs
    simpa using inv_mem_lpsGenerators401_of_mem q hq hs
  · exact inv_mem_lpsGenerators401_of_mem q hq
end QEC.Coding.BalancedProduct.LPSGenerators
