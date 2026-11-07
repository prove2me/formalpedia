-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.mapRows_left_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:19.4232+00:00
-- url     : https://prove2.me/submissions/d81b46a6-0a0e-426c-a2ae-34b410aac421

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq F] [Fintype W]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    {I J : Type v} [Fintype I]
    (T : Word F W →ₗ[F] Word F W)
    (H : Matrix J I F) (x : Matrix I W F) :
    mapRows T (H * x) = H * mapRows T x := by
  ext j k
  have hRow : (H * x) j = ∑ i : I, H j i • x i := by
    funext t
    simp [Matrix.mul_apply, Pi.smul_apply]
  simp [mapRows, hRow, map_sum, Matrix.mul_apply, Pi.smul_apply]
end QEC.Coding.ProductExpansion
