-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.dressedZDistanceAtLeast_of_middleHomologyDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:03.832477+00:00
-- url     : https://prove2.me/submissions/a2a83538-af40-4593-9173-73469a239c10

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CSS_Subsystem

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
    (h : MiddleHomologyDistanceAtLeast D.complex d) :
    D.DressedZDistanceAtLeast d := by
  intro z hz hProjected
  apply h z hz
  intro hzBoundary
  apply hProjected
  have hClassZero :
      D.complex.middleBoundaryInCycles.mkQ
          (⟨z, hz⟩ : D.complex.middleCycleCode.carrier) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero
      D.complex.middleBoundaryInCycles).2
    exact hzBoundary
  rw [hClassZero, map_zero]
end QEC.Coding.SubsystemCSSData
