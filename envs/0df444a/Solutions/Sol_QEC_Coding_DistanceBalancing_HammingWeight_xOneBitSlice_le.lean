-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.HammingWeight_xOneBitSlice_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:50.150124+00:00
-- url     : https://prove2.me/submissions/1db1130c-065d-4145-8f49-1388fdbcaaeb

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) :
    HammingWeight (xOneBitSlice z a) ≤ HammingWeight z := by
  classical
  let f : {x1 : xOne // xOneBitSlice z a x1 ≠ 0} →
      {q : QubitIndex xOne xTwo classicalBit classicalCheck // z q ≠ 0} :=
    fun x1 => ⟨Sum.inl (x1.1, a), x1.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun q => q.1) hxy
    have hp := Sum.inl.inj h
    exact congrArg Prod.fst hp
  calc
    HammingWeight (xOneBitSlice z a) =
        Fintype.card {x1 : xOne // xOneBitSlice z a x1 ≠ 0} := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ ≤ Fintype.card
        {q : QubitIndex xOne xTwo classicalBit classicalCheck // z q ≠ 0} :=
      Fintype.card_le_of_injective f hf
    _ = HammingWeight z := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
end QEC.Coding.DistanceBalancing
