-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.dual_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:40:38.588236+00:00
-- url     : https://prove2.me/submissions/9ff70d67-9e45-4023-accb-a3bb7aa4d7e5

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
    D.dual.complex = dualChainComplex D.complex := rfl
end QEC.Coding.SubsystemCSSData
