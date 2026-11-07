-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.mem_middleBoundaryCode_of_slices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:50:30.223707+00:00
-- url     : https://prove2.me/submissions/7f08389f-76c5-4670-9b37-0728588c443c

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_residualLift
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
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    z ∈ (chainComplex D).middleBoundaryCode.carrier := by
  apply ((chainComplex D).mem_middleBoundaryCode_iff z).2
  refine ⟨productSliceFilling D z hFill + residualLift D S z hFill, ?_⟩
  rw [map_add]
  change boundary2 D (productSliceFilling D z hFill) +
    boundary2 D (residualLift D S z hFill) = z
  rw [boundary2_residualLift D S hS z hz hFill]
  ext q
  simp only [sliceRemainder, Pi.add_apply]
  calc
    boundary2 D (productSliceFilling D z hFill) q +
        (z q + boundary2 D (productSliceFilling D z hFill) q) =
      z q +
        (boundary2 D (productSliceFilling D z hFill) q +
          boundary2 D (productSliceFilling D z hFill) q) := by
      ac_rfl
    _ = z q := by rw [ZModModule.add_self, add_zero]
end QEC.Coding.DistanceBalancing
