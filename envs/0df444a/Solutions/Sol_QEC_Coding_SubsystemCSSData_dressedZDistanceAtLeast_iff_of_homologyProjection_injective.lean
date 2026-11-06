-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.dressedZDistanceAtLeast_iff_of_homologyProjection_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:17.616681+00:00
-- url     : https://prove2.me/submissions/38e92b7f-e746-44d1-b5cf-68aa7f006a71

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Theorems.Thm_QEC_Coding_SubsystemCSSData_dressedZDistanceAtLeast_of_middleHomologyDistanceAtLeast
import Theorems.Thm_QEC_Coding_SubsystemCSSData_middleHomologyDistanceAtLeast_of_dressedZDistanceAtLeast

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
    (hInjective : Function.Injective D.homologyProjection) :
    D.DressedZDistanceAtLeast d ↔
      MiddleHomologyDistanceAtLeast D.complex d := by
  constructor
  · exact D.middleHomologyDistanceAtLeast_of_dressedZDistanceAtLeast d hInjective
  · exact D.dressedZDistanceAtLeast_of_middleHomologyDistanceAtLeast d
end QEC.Coding.SubsystemCSSData
