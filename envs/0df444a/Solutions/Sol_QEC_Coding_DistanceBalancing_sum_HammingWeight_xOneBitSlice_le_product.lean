-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.sum_HammingWeight_xOneBitSlice_le_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:39.84439+00:00
-- url     : https://prove2.me/submissions/abff33db-4e6a-46c2-8777-4028180629cc

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
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck)) :
    (∑ a : classicalBit, HammingWeight (xOneBitSlice x a)) ≤
      HammingWeight x := by
  classical
  let f : (Σ a : classicalBit,
      {x1 : xOne // xOneBitSlice x a x1 ≠ 0}) →
      {q : QubitIndex xOne xTwo classicalBit classicalCheck // x q ≠ 0} :=
    fun p => ⟨Sum.inl (p.2.1, p.1), p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, ⟨x1, hx1⟩⟩ ⟨a', ⟨x1', hx1'⟩⟩ h
    have hp := Sum.inl.inj (congrArg (fun q => q.1) h)
    have ha : a = a' := congrArg Prod.snd hp
    subst a'
    have hx : x1 = x1' := congrArg Prod.fst hp
    subst x1'
    rfl
  calc
    (∑ a : classicalBit, HammingWeight (xOneBitSlice x a)) =
        Fintype.card (Σ a : classicalBit,
          {x1 : xOne // xOneBitSlice x a x1 ≠ 0}) := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
    _ ≤ Fintype.card
        {q : QubitIndex xOne xTwo classicalBit classicalCheck // x q ≠ 0} :=
      Fintype.card_le_of_injective f hf
    _ = HammingWeight x := by
      simp [HammingWeight, hammingSupport, Fintype.card_subtype]
end QEC.Coding.DistanceBalancing
