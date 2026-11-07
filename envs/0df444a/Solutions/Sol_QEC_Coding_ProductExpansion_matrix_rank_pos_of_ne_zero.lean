-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.matrix_rank_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:53.628208+00:00
-- url     : https://prove2.me/submissions/19379085-647a-4167-bcd2-f58e1cfbc551

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
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
omit [Fintype F] [DecidableEq F] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    {I : Type v} [Fintype I]
    (M : Matrix I W F) (hM : M ≠ 0) :
    0 < M.rank := by
  classical
  by_contra hNot
  have hRankZero : M.rank = 0 := by omega
  have hRangeBot : LinearMap.range M.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hRankZero
  have hMapZero : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp hRangeBot
  apply hM
  ext i j
  have hAt := congrArg (fun f : (W → F) →ₗ[F] (I → F) =>
    f (Pi.single j (1 : F)) i) hMapZero
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hAt
end QEC.Coding.ProductExpansion
