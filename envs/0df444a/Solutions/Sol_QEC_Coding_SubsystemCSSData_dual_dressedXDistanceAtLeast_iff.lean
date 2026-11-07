-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.dual_dressedXDistanceAtLeast_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:48.586459+00:00
-- url     : https://prove2.me/submissions/736dbf39-3578-4999-b7e5-7a61fb0d39e1

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Theorems.Thm_QEC_Coding_SubsystemCSSData_dual_complex
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Coding_wordLinearMapTranspose_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.SubsystemCSSData.dual_complex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SubsystemCSSData
universe u v
variable {i0 i1 i2 : Type u} {LogicalZ LogicalX : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]
namespace QEC.Coding.SubsystemCSSData
theorem _root_.solution
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat) :
    D.dual.DressedXDistanceAtLeast d ↔ D.DressedZDistanceAtLeast d := by
  constructor
  · intro h z hz hLogical
    apply h z (by
      change z ∈ (dualChainComplex D.complex).middleCocycleCode.carrier
      rw [(dualChainComplex D.complex).mem_middleCocycleCode_iff]
      simpa only [dualChainComplex_boundary2,
        wordLinearMapTranspose_transpose] using
          (D.complex.mem_middleCycleCode_iff z).mp hz)
    change D.homologyProjection
      (dualCohomologyToOriginalHomology D.complex
        ((dualChainComplex D.complex).middleCoboundaryInCocycles.mkQ
          ⟨z, _⟩)) ≠ 0
    rw [dualCohomologyToOriginalHomology_mk]
    exact hLogical
  · intro h x hx hLogical
    apply h x (by
      rw [D.complex.mem_middleCycleCode_iff]
      have hx' : x ∈ (dualChainComplex D.complex).middleCocycleCode.carrier := by
        exact hx
      have hx' := ((dualChainComplex D.complex).mem_middleCocycleCode_iff x).mp hx'
      simpa only [dualChainComplex_boundary2,
        wordLinearMapTranspose_transpose] using hx')
    change D.homologyProjection
      (D.complex.middleBoundaryInCycles.mkQ ⟨x, _⟩) ≠ 0
    change D.homologyProjection
      (dualCohomologyToOriginalHomology D.complex
        ((dualChainComplex D.complex).middleCoboundaryInCocycles.mkQ
          ⟨x, hx⟩)) ≠ 0 at hLogical
    simpa only [dualCohomologyToOriginalHomology_mk] using hLogical
end QEC.Coding.SubsystemCSSData
