-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGenerators.lpsGenerators401_ne_conj_upperUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:56:07.151212+00:00
-- url     : https://prove2.me/submissions/eb0c1005-a276-45fe-a6fc-cc5c35ba98b8

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_not_projectiveDetIsSquare_of_mem_lpsGenerators401
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_ne_conj_upperUnipotent_of_not_detSquare


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
    (hs : s ∈ lpsGenerators401 q hq)
    (g : PGL(2, ZMod q)) (x : ZMod q) :
    s ≠ g * upperUnipotentPGL x * g⁻¹ :=
  ne_conj_upperUnipotent_of_not_detSquare
    (not_projectiveDetIsSquare_of_mem_lpsGenerators401 q hq hs) g x
end QEC.Coding.BalancedProduct.LPSGenerators
