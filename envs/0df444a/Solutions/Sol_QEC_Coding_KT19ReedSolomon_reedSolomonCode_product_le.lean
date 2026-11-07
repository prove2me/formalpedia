-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.reedSolomonCode_product_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:57:02.700956+00:00
-- url     : https://prove2.me/submissions/8bca2443-b216-45c4-89e8-1c29b9216400

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
section
noncomputable section
namespace QEC
namespace Coding
namespace KT19ReedSolomon
open scoped BigOperators
private theorem evaluationLinearMap_mul (p l m : Nat) [Fact p.Prime]
    (left : Polynomial.degreeLT (ZMod p) l)
    (right : Polynomial.degreeLT (ZMod p) m) :
    coordinatewiseProduct (evaluationLinearMap p l left) (evaluationLinearMap p m right) =
      evaluationLinearMap p (l + m - 1) ⟨left.1 * right.1,
        mul_mem_degreeLT p l m left right⟩ := by
  funext point
  simp [coordinatewiseProduct, evaluationMap]
end KT19ReedSolomon
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p l m : Nat) [Fact p.Prime] :
    (coordinatewiseProductCode (reedSolomonCode p l) (reedSolomonCode p m)).carrier ≤
      (reedSolomonCode p (l + m - 1)).carrier := by
  rw [coordinatewiseProductCode]
  apply Submodule.span_le.2
  rintro word ⟨x, hx, y, hy, rfl⟩
  rcases (mem_reedSolomonCode p l x).1 hx with ⟨left, rfl⟩
  rcases (mem_reedSolomonCode p m y).1 hy with ⟨right, rfl⟩
  rw [evaluationLinearMap_mul]
  exact evaluation_mem_reedSolomonCode p (l + m - 1) _
end QEC.Coding.KT19ReedSolomon
