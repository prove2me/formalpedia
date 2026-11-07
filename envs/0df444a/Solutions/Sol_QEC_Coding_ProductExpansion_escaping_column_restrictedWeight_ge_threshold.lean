-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.escaping_column_restrictedWeight_ge_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:01:51.853196+00:00
-- url     : https://prove2.me/submissions/f63e0610-91fd-4929-b93a-a5e2ccb653a6

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
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_syndromeBasis_of_rank_sized
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_generator_coordinate_outside_span
import Theorems.Thm_QEC_Coding_ProductExpansion_generator_weight_le_replacement_of_minimal
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
omit [Fintype F] [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W) (d : Nat)
    (C : Finset (Word F W))
    (hCard : C.card = (h' * x).rank)
    (hSpanning : ∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C)
    (hMin : ∀ D : Finset (Word F W),
      D.card = (h' * x).rank →
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
      generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D)
    (j : W) (hj : j ∈ columnsOutsideSyndromeSpan h' x (lightGenerators A C d)) :
    d ≤ 6 * C.card * restrictedHammingWeight A (column x j) := by
  classical
  obtain ⟨b, hb⟩ := exists_syndromeBasis_of_rank_sized h' x C hCard hSpanning
  have hjOutside : h'.mulVec (column x j) ∉ syndromeSpan h' (lightGenerators A C d) := by
    simpa [columnsOutsideSyndromeSpan, columnsWithSyndromeInSpan] using hj
  obtain ⟨c, hcNotLight, hcCoordinate⟩ := exists_generator_coordinate_outside_span
    h' C (lightGenerators A C d) b hb
    ⟨h'.mulVec (column x j), hSpanning j⟩ hjOutside
  have hcWeight := generator_weight_le_replacement_of_minimal
    h' x A C hCard hSpanning hMin b hb c j hcCoordinate
  have hcHeavy : d ≤ 6 * C.card * restrictedHammingWeight A c.1 := by
    by_contra hlt
    apply hcNotLight
    change c.1 ∈ C.filter (fun y => 6 * C.card * restrictedHammingWeight A y < d)
    exact Finset.mem_filter.mpr ⟨c.2, by omega⟩
  exact hcHeavy.trans (Nat.mul_le_mul_left (6 * C.card) hcWeight)
end QEC.Coding.ProductExpansion
