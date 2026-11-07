-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_generatorSupport_inter_le_generatorRestrictedWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:33:03.686396+00:00
-- url     : https://prove2.me/submissions/1bc7b62e-50eb-4190-8e0c-5f5675b33fbd

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
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (A : Finset W) (C : Finset (Word F W)) :
    (generatorSupportOn A C).card ≤ generatorRestrictedWeight A C := by
  classical
  unfold generatorSupportOn
  have hSubset : generatorSupport C ∩ A ⊆
      C.biUnion (fun y => hammingSupport y ∩ A) := by
    intro i hi
    obtain ⟨hiSupport, hiA⟩ := Finset.mem_inter.mp hi
    obtain ⟨y, hyC, hiy⟩ := Finset.mem_biUnion.mp hiSupport
    exact Finset.mem_biUnion.mpr ⟨y, hyC,
      Finset.mem_inter.mpr ⟨hiy, hiA⟩⟩
  calc
    (generatorSupport C ∩ A).card ≤
        (C.biUnion (fun y => hammingSupport y ∩ A)).card :=
      Finset.card_le_card hSubset
    _ ≤ ∑ y ∈ C, (hammingSupport y ∩ A).card := Finset.card_biUnion_le
    _ = generatorRestrictedWeight A C := by
      unfold generatorRestrictedWeight
      apply Finset.sum_congr rfl
      intro y _
      have hInter : hammingSupport y ∩ A =
          A.filter (fun i => y i ≠ 0) := by
        ext i
        simp [hammingSupport, and_comm]
      rw [hInter]
      unfold restrictedHammingWeight
      calc
        (A.filter (fun i => y i ≠ 0)).card =
            ∑ i ∈ A, if y i ≠ 0 then 1 else 0 := by
          simpa using (Finset.sum_boole (R := Nat) (fun i => y i ≠ 0) A).symm
        _ = ∑ i ∈ A, if y i = 0 then 0 else 1 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : y i = 0 <;> simp [hi]
end QEC.Coding.ProductExpansion
