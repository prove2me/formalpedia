-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_conjDensity_of_transportedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:34:23.523688+00:00
-- url     : https://prove2.me/submissions/723b279d-d035-49cf-a62e-ddc9868d9d84

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.DensityOperator
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {rho : DensityOperator H} (hCD : QuantumCode.TransportedBy U C D)
    (hρ : SupportedOn C rho) :
    SupportedOn D (U.conjDensity rho) := by
  intro y
  rw [UnitaryTransport.conjDensity_apply]
  exact (hCD (rho.toOperator (U.toLinearEquiv.symm y))).1
    (hρ (U.toLinearEquiv.symm y))
end QEC.Semantics.DensityOperator
