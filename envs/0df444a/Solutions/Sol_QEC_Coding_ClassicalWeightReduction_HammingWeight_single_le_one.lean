-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.HammingWeight_single_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:20.197115+00:00
-- url     : https://prove2.me/submissions/0d3261fa-0e25-4f8c-97ef-f1d8942701bb

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (i : Index) :
    HammingWeight (Pi.single i (1 : F) : Word F Index) ≤ 1 := by
  classical
  rw [HammingWeight_eq_card_hammingSupport]
  calc
    (hammingSupport (Pi.single i (1 : F) : Word F Index)).card ≤
        ({i} : Finset Index).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_singleton]
      by_contra hji
      have hzero : (Pi.single i (1 : F) : Word F Index) j = 0 := by
        rw [Pi.single_eq_of_ne hji]
      simp [hammingSupport, hzero] at hj
    _ = 1 := Finset.card_singleton i
end QEC.Coding.ClassicalWeightReduction
