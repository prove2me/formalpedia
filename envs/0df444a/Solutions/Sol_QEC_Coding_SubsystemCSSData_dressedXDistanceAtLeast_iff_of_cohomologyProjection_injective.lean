-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.dressedXDistanceAtLeast_iff_of_cohomologyProjection_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:22.553429+00:00
-- url     : https://prove2.me/submissions/40465aac-7c31-40e9-9202-c63e326c4a2b

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Theorems.Thm_QEC_Coding_SubsystemCSSData_dressedXDistanceAtLeast_of_middleCohomologyDistanceAtLeast
import Theorems.Thm_QEC_Coding_SubsystemCSSData_middleCohomologyDistanceAtLeast_of_dressedXDistanceAtLeast

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
    (hInjective : Function.Injective D.cohomologyProjection) :
    D.DressedXDistanceAtLeast d ↔
      MiddleCohomologyDistanceAtLeast D.complex d := by
  constructor
  · exact D.middleCohomologyDistanceAtLeast_of_dressedXDistanceAtLeast d hInjective
  · exact D.dressedXDistanceAtLeast_of_middleCohomologyDistanceAtLeast d
end QEC.Coding.SubsystemCSSData
