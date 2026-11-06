-- Prove2me | solution 1 for QEC.Coding.SubsystemCSSData.dressedXDistanceAtLeast_of_middleCohomologyDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:36:06.563212+00:00
-- url     : https://prove2.me/submissions/8d563bc1-e695-437e-b3eb-c8b78a96baf1

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
    (h : MiddleCohomologyDistanceAtLeast D.complex d) :
    D.DressedXDistanceAtLeast d := by
  intro x hx hProjected
  apply h x hx
  intro hxCoboundary
  apply hProjected
  have hClassZero :
      D.complex.middleCoboundaryInCocycles.mkQ
          (⟨x, hx⟩ : D.complex.middleCocycleCode.carrier) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero
      D.complex.middleCoboundaryInCocycles).2
    exact hxCoboundary
  rw [hClassZero, map_zero]
end QEC.Coding.SubsystemCSSData
