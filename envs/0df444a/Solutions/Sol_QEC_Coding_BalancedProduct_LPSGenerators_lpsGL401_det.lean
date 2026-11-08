-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.lpsGL401_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:51:26.948444+00:00
-- url     : https://prove2.me/submissions/c3e94213-6e12-43e2-8fc9-a5aea27715e7

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
    (t : ShellIndex401) (ht : t ∈ shell401) :
    ((lpsGL401 q hq t ht).det : ZMod q) = (401 : ZMod q) := by
  change (lpsMatrix401 q t).det = (401 : ZMod q)
  exact det_lpsMatrix401 q t ht
end QEC.Coding.BalancedProduct.LPSGenerators
