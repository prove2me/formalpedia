-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.logicalQubits_eq_cohomology_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:07.847672+00:00
-- url     : https://prove2.me/submissions/fdc45886-6208-4d3d-a3bd-bab931f443e4

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
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    D.logicalQubits = Module.finrank (ZMod 2) LogicalX :=
  D.logical_finrank_eq
end QEC.Coding.SubsystemCSSData
