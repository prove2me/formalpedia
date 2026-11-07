-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.codeword_eq_zero_of_minimality_and_small_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:40.206743+00:00
-- url     : https://prove2.me/submissions/57ce2b71-aa01-4503-8296-a9b2ad7b2a50

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_sub_le
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (x c : Word F W)
    (hc : c ∈ (parityCheckCode h).carrier)
    (hGap : 2 * (HammingWeight (x - c) : ℝ) + delta < d)
    (hMinimal : (HammingWeight x : ℝ) ≤ HammingWeight (x - c) + delta) :
    c = 0 := by
  by_contra hNonzero
  have hDistanceNat := hDistance c hc hNonzero
  have hCodeword : c = x - (x - c) := by
    ext j
    simp
  have hTriangleNat : HammingWeight c ≤ HammingWeight x + HammingWeight (x - c) := by
    calc
      HammingWeight c = HammingWeight (x - (x - c)) := congrArg HammingWeight hCodeword
      _ ≤ HammingWeight x + HammingWeight (x - c) := HammingWeight_sub_le x (x - c)
  have hDistanceReal : (d : ℝ) ≤ HammingWeight c := by exact_mod_cast hDistanceNat
  have hTriangleReal : (HammingWeight c : ℝ) ≤
      HammingWeight x + HammingWeight (x - c) := by exact_mod_cast hTriangleNat
  linarith
end QEC.Coding.ProductExpansion
