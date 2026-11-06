-- Prove2me | solution 1 for QEC.Coding.HammingWeight_linearMap_le_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:32.70343+00:00
-- url     : https://prove2.me/submissions/f1da02d8-3776-4b53-bb1d-2885a52799f9

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_HammingWeight_smul_le
import Theorems.Thm_QEC_Coding_HammingWeight_finset_sum_le
import Theorems.Thm_QEC_Coding_word_eq_sum_hammingSupport_single
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
namespace QEC.Coding
theorem _root_.solution
    {F : Type u} [Field F] [DecidableEq F]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {κ : Type w} [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ) (L : Nat)
    (hBasis : ∀ i : ι, HammingWeight (f (Pi.single i 1)) ≤ L)
    (x : Word F ι) :
    HammingWeight (f x) ≤ L * HammingWeight x := by
  classical
  have hx := word_eq_sum_hammingSupport_single x
  calc
    HammingWeight (f x) =
        HammingWeight (f (∑ i ∈ hammingSupport x,
          Pi.single i (x i))) := by rw [← hx]
    _ = HammingWeight (∑ i ∈ hammingSupport x,
          f (Pi.single i (x i))) := by rw [map_sum]
    _ ≤
        ∑ i ∈ hammingSupport x,
          HammingWeight (f (Pi.single i (x i))) :=
      HammingWeight_finset_sum_le _ _
    _ ≤ ∑ _i ∈ hammingSupport x, L := by
      apply Finset.sum_le_sum
      intro i hi
      have hsingle : (Pi.single i (x i) : Word F ι) =
          x i • Pi.single i (1 : F) := by
        ext j
        simp [Pi.single_apply]
      rw [hsingle, f.map_smul]
      exact (HammingWeight_smul_le _ _).trans (hBasis i)
    _ = L * HammingWeight x := by
      simp [HammingWeight, Nat.mul_comm]
end QEC.Coding
