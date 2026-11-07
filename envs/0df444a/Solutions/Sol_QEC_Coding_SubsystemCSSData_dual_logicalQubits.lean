-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.dual_logicalQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:57.982339+00:00
-- url     : https://prove2.me/submissions/cb7b7017-904d-4589-9003-94bb255fe6a8

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CSS_SubsystemDual

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
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    D.dual.logicalQubits = D.logicalQubits := by
  exact D.logical_finrank_eq.symm
end QEC.Coding.SubsystemCSSData
