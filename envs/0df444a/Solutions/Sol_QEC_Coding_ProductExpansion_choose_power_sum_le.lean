-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.choose_power_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:34.63121+00:00
-- url     : https://prove2.me/submissions/b3dd8f8f-841f-4c4e-9255-6899c6338677

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (n out s q : Nat) (hq : 0 < q) :
    (∑ t : Fin s, Nat.choose n t.1 * q ^ (out + t.1)) ≤
      s * (n + 1) ^ s * q ^ (out + s) := by
  classical
  have hEach (t : Fin s) :
      Nat.choose n t.1 * q ^ (out + t.1) ≤
        (n + 1) ^ s * q ^ (out + s) := by
    have hChoose : Nat.choose n t.1 ≤ (n + 1) ^ s := by
      exact (Nat.choose_le_pow n t.1).trans <|
        (Nat.pow_le_pow_left (Nat.le_add_right n 1) t.1).trans
          (Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_of_lt t.2))
    have hPow : q ^ (out + t.1) ≤ q ^ (out + s) :=
      Nat.pow_le_pow_right hq (Nat.add_le_add_left (Nat.le_of_lt t.2) out)
    exact Nat.mul_le_mul hChoose hPow
  have hSum := Finset.sum_le_card_nsmul Finset.univ
    (fun t : Fin s => Nat.choose n t.1 * q ^ (out + t.1))
    ((n + 1) ^ s * q ^ (out + s)) (fun t _ => hEach t)
  simpa [nsmul_eq_mul, mul_assoc] using hSum
end QEC.Coding.ProductExpansion
