-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.inv_mem_lpsGenerators401_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:01:22.406428+00:00
-- url     : https://prove2.me/submissions/9f34709a-3795-4fc2-989a-d7fb07e6ef28

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGenerator401_conj_eq_inv
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
    s⁻¹ ∈ lpsGenerators401 q hq := by
  rcases (mem_lpsGenerators401_iff q hq s).mp hs with ⟨t, ht, rfl⟩
  apply (mem_lpsGenerators401_iff q hq _).mpr
  refine ⟨t.conj, (ShellIndex401.conj_mem_shell401_iff t).mpr ht, ?_⟩
  exact lpsGenerator401_conj_eq_inv q hq t ht
end QEC.Coding.BalancedProduct.LPSGenerators
