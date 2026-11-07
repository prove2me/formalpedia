-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.reedSolomonCode_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:17:23.678248+00:00
-- url     : https://prove2.me/submissions/1fe6bfab-b9cf-4a66-809c-4a366f3638a8

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
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
private theorem sum_evaluation_eq_zero (p : Nat) [Fact p.Prime]
    (polynomial : Polynomial.degreeLT (ZMod p) (p - 1)) :
    ∑ point : ZMod p, polynomial.1.eval point = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_degreeLTEquiv polynomial.2]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro exponent _
  rw [← Finset.mul_sum]
  have hsum : ∑ point : ZMod p, point ^ (exponent : Nat) = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) (exponent : Nat)
      (by simpa [ZMod.card] using exponent.isLt)
  rw [hsum, mul_zero]
private theorem reedSolomonCode_le_dual_complementary (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) :
    (reedSolomonCode p (p - l)).carrier ≤ (reedSolomonCode p l).dual.carrier := by
  intro word hword
  refine ((reedSolomonCode p l).mem_dual word).2 ?_
  intro other hother
  rcases (mem_reedSolomonCode p (p - l) word).1 hword with ⟨left, rfl⟩
  rcases (mem_reedSolomonCode p l other).1 hother with ⟨right, rfl⟩
  rw [wordPairing_apply]
  change ∑ point : ZMod p,
    coordinatewiseProduct (evaluationLinearMap p (p - l) left)
      (evaluationLinearMap p l right) point = 0
  rw [evaluationLinearMap_mul p (p - l) l left right]
  have hbound : p - l + l - 1 = p - 1 := by omega
  let product : Polynomial.degreeLT (ZMod p) (p - 1) :=
    ⟨left.1 * right.1, by
      rw [← hbound]
      exact mul_mem_degreeLT p (p - l) l left right⟩
  change ∑ point : ZMod p, (left.1 * right.1).eval point = 0
  exact sum_evaluation_eq_zero p product
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
theorem _root_.solution (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) :
    (reedSolomonCode p l).dual.carrier = (reedSolomonCode p (p - l)).carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact reedSolomonCode_le_dual_complementary p l hlp
  · change Dimension (reedSolomonCode p (p - l)) = Dimension (reedSolomonCode p l).dual
    rw [LinearCode.dual_dimension_eq_length_sub_dimension,
      reedSolomonCode_dimension p l hlp,
      reedSolomonCode_dimension p (p - l) (Nat.sub_le _ _)]
    change p - l = Fintype.card (ZMod p) - l
    simp [ZMod.card]
end QEC.Coding.KT19ReedSolomon
