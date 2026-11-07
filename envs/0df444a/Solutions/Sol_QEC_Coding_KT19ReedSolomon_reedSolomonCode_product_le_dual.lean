-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.reedSolomonCode_product_le_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:58.10493+00:00
-- url     : https://prove2.me/submissions/e3faee6d-24da-4583-9c86-822d320aeb28

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_product_le
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dual
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p l : Nat) [Fact p.Prime]
    (hproduct : 3 * l ≤ p + 1) :
    (coordinatewiseProductCode (reedSolomonCode p l) (reedSolomonCode p l)).carrier ≤
      (reedSolomonCode p l).dual.carrier := by
  rw [reedSolomonCode_dual p l (by omega)]
  refine (reedSolomonCode_product_le p l l).trans ?_
  have hdegree : l + l - 1 ≤ p - l := by omega
  intro word hword
  rcases (mem_reedSolomonCode p (l + l - 1) word).1 hword with ⟨polynomial, rfl⟩
  exact evaluation_mem_reedSolomonCode p (p - l)
    ⟨polynomial.1, Polynomial.mem_degreeLT.mpr
      ((Polynomial.mem_degreeLT.mp polynomial.2).trans_le (by exact_mod_cast hdegree))⟩
end QEC.Coding.KT19ReedSolomon
