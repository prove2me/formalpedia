-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.mem_lpsGenerators401_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:51:28.433524+00:00
-- url     : https://prove2.me/submissions/c1b15932-06a2-42c8-b4b4-86b38e442d4f

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators

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
    s ∈ lpsGenerators401 q hq ↔
      ∃ t : ShellIndex401, ∃ ht : t ∈ shell401,
        lpsGenerator401 q hq t ht = s := by
  classical
  simp [lpsGenerators401]
end QEC.Coding.BalancedProduct.LPSGenerators
