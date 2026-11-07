-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.column_adjustment_eq_zero_of_small_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:59:53.340454+00:00
-- url     : https://prove2.me/submissions/99505c6d-fae7-4be5-ac97-a7e3148d6cad

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_codeword_eq_zero_of_minimality_and_small_residual
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (j : W) (c : Word F W) (hc : c ∈ (parityCheckCode h').carrier)
    (hSmall : (HammingWeight (column x j + c) : ℝ) < (d : ℝ) / 3) :
    c = 0 := by
  have hNegative : -c ∈ (parityCheckCode h').carrier :=
    (parityCheckCode h').carrier.neg_mem hc
  have hGap : 2 * (HammingWeight (column x j - -c) : ℝ) + (d : ℝ) / 3 < d := by
    simpa only [sub_neg_eq_add] using (show
      2 * (HammingWeight (column x j + c) : ℝ) + (d : ℝ) / 3 < d by
        linarith)
  have hMinimalColumn : (HammingWeight (column x j) : ℝ) ≤
      HammingWeight (column x j - -c) + (d : ℝ) / 3 := by
    simpa only [sub_neg_eq_add] using hMinimal.2 j c hc
  have hZero := codeword_eq_zero_of_minimality_and_small_residual
    h' d hDistance' ((d : ℝ) / 3) (column x j) (-c)
      hNegative hGap hMinimalColumn
  simpa using hZero
end QEC.Coding.ProductExpansion
