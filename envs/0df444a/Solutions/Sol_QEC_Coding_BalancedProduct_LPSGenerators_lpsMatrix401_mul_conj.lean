-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.lpsMatrix401_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:54:03.340213+00:00
-- url     : https://prove2.me/submissions/e2b0d14d-9d70-4792-ad1d-0a284505155b

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsMatrix401_conj

set_option autoImplicit false
open scoped BigOperators
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGenerators
open Matrix
open LPSArithmetic
namespace QEC.Coding.BalancedProduct.LPSGenerators
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (t : ShellIndex401) (ht : t ∈ shell401) :
    lpsMatrix401 q t * lpsMatrix401 q t.conj =
      (401 : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  rw [lpsMatrix401_conj, Matrix.mul_adjugate, det_lpsMatrix401 q t ht]
end QEC.Coding.BalancedProduct.LPSGenerators
