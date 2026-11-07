-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.generatorRestrictedWeight_ge_one_sixth_of_large_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:57:19.973837+00:00
-- url     : https://prove2.me/submissions/ccefbace-c50d-4a9a-8e62-f99ff8e10bae

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
import Theorems.Thm_QEC_Coding_ProductExpansion_card_generatorSupport_inter_le_generatorRestrictedWeight
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
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (d m : Nat) (hLength : d ≤ Fintype.card W) (hSmallM : 6 * m ≤ d)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hSupport : (d : ℝ) / 3 ≤ (generatorSupport C).card) :
    (d : ℝ) / 6 ≤ generatorRestrictedWeight A C := by
  classical
  let S := generatorSupport C
  have hWeight := card_generatorSupport_inter_le_generatorRestrictedWeight A C
  change (S ∩ A).card ≤ generatorRestrictedWeight A C at hWeight
  have hSdiffSubset : S \ A ⊆ Finset.univ \ A := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  have hSdiffCard := Finset.card_le_card hSdiffSubset
  have hComplement : (Finset.univ \ A).card = Fintype.card W - A.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ A)
  rw [hComplement] at hSdiffCard
  have hComplementSmall : Fintype.card W - A.card ≤ m := by omega
  have hSCard : S.card = (S ∩ A).card + (S \ A).card := by
    exact (Finset.card_inter_add_card_sdiff S A).symm
  have hSupportNat : S.card ≤ generatorRestrictedWeight A C + m := by omega
  have hSupportReal : (d : ℝ) / 3 ≤ S.card := hSupport
  have hSupportBoundReal : (S.card : ℝ) ≤ generatorRestrictedWeight A C + m := by
    exact_mod_cast hSupportNat
  have hSmallMReal : (6 : ℝ) * m ≤ d := by exact_mod_cast hSmallM
  linarith
end QEC.Coding.ProductExpansion
