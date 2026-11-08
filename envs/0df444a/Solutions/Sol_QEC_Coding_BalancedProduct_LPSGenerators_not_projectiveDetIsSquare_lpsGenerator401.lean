-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.not_projectiveDetIsSquare_lpsGenerator401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:54:48.992984+00:00
-- url     : https://prove2.me/submissions/7d395549-a279-4b9d-bd2b-546ac1241a32

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_lpsGL401_det
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_not_projectiveDetIsSquare_mk_of_det_401


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
    ¬ ProjectiveDetIsSquare (lpsGenerator401 q hq t ht) := by
  exact not_projectiveDetIsSquare_mk_of_det_401
    (lpsGL401 q hq t ht) (lpsGL401_det q hq t ht) hq
end QEC.Coding.BalancedProduct.LPSGenerators
