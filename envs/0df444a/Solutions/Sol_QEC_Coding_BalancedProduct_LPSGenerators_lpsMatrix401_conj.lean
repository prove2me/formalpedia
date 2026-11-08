-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.lpsMatrix401_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:53:23.764058+00:00
-- url     : https://prove2.me/submissions/6d32015e-5c69-40d2-8730-4eb5aaec908f

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
    (q : ℕ) [Fact q.Prime] (t : ShellIndex401) :
    lpsMatrix401 q t.conj = (lpsMatrix401 q t).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsMatrix401, Matrix.adjugate_fin_two] <;> ring
end QEC.Coding.BalancedProduct.LPSGenerators
