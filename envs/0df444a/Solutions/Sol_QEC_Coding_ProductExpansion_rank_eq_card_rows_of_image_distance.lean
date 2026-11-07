-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.rank_eq_card_rows_of_image_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:16.472661+00:00
-- url     : https://prove2.me/submissions/86ca99e8-dc6e-47a8-8786-9995f00356ad

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_generatorMap_injective_of_image_distance
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
omit [Fintype F] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (g : Matrix R W F) (d : Nat) (hPositive : 0 < d)
    (hImage : ∀ a : Word F R, a ≠ 0 →
      d ≤ HammingWeight (g.transpose.mulVec a)) :
    g.rank = Fintype.card R := by
  classical
  rw [← Matrix.rank_transpose]
  change Module.finrank F (LinearMap.range (Matrix.toLin' g.transpose)) =
    Fintype.card R
  rw [LinearMap.finrank_range_of_inj
    (by
      intro a b hab
      apply generatorMap_injective_of_image_distance g d hPositive hImage
      simpa only [Matrix.toLin'_apply] using hab)]
  simp
end QEC.Coding.ProductExpansion
