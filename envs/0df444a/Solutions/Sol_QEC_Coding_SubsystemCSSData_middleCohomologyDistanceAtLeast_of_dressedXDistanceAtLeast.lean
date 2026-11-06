-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.middleCohomologyDistanceAtLeast_of_dressedXDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:07.781259+00:00
-- url     : https://prove2.me/submissions/ae7f5644-f25b-4b86-b432-21c7d5f694ad

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding
universe u v
open QEC.Coding.SubsystemCSSData
variable {i0 i1 i2 : Type u} {LogicalZ LogicalX : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ] [Module.Finite (ZMod 2) LogicalX]
namespace QEC.Coding.SubsystemCSSData
theorem _root_.solution
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.cohomologyProjection)
    (h : D.DressedXDistanceAtLeast d) :
    MiddleCohomologyDistanceAtLeast D.complex d := by
  intro x hx hxNotCoboundary
  apply h x hx
  intro hProjectedZero
  have hClassZero :
      D.complex.middleCoboundaryInCocycles.mkQ
          (⟨x, hx⟩ : D.complex.middleCocycleCode.carrier) = 0 := by
    apply hInjective
    simpa using hProjectedZero
  have hxGauge :
      (⟨x, hx⟩ : D.complex.middleCocycleCode.carrier) ∈
        D.complex.middleCoboundaryInCocycles :=
    (Submodule.Quotient.mk_eq_zero
      D.complex.middleCoboundaryInCocycles).1 hClassZero
  exact hxNotCoboundary hxGauge
end QEC.Coding.SubsystemCSSData
