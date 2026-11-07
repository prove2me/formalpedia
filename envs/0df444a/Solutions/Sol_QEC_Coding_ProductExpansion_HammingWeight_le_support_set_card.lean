-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.HammingWeight_le_support_set_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:35.494956+00:00
-- url     : https://prove2.me/submissions/8cf329e8-9b16-4cbe-bd8e-9f8e263ed880

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
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (S : Finset W) (x : Word F W) (hSupport : ∀ i ∉ S, x i = 0) :
    HammingWeight x ≤ S.card := by
  classical
  have hSubset : hammingSupport x ⊆ S := by
    intro i hi
    by_contra hiS
    have hxi : x i ≠ 0 := by simpa [hammingSupport] using hi
    exact hxi (hSupport i hiS)
  exact Finset.card_le_card hSubset
end QEC.Coding.ProductExpansion
