-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.supportedOn_conjDensity_transport_iff
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T15:56:23.326231+00:00
-- url     : https://prove2.me/submissions/6e1691d7-66a6-4da9-a81a-bdb9e6d8a590

-- ID: 4d8f27ee-c84e-4de7-8d02-b11e772632d3 | NAME: QEC.Semantics.DensityOperator.supportedOn_conjDensity_transport_iff | 未本地编译验证
import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.DensityOperator
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem solution (U : UnitaryTransport H K) (C : QuantumCode H) (rho : DensityOperator H) :
    SupportedOn (C.transport U) (U.conjDensity rho) ↔ SupportedOn C rho := by
  constructor
  · intro h v
    have hw : U.toLinearEquiv (rho.toOperator v) ∈
        C.carrier.map U.toLinearEquiv.toLinearMap := by
      simpa [QuantumCode.transport, UnitaryTransport.conjDensity,
        UnitaryTransport.conjOperator_apply] using h (U.toLinearEquiv v)
    rcases hw with ⟨y, hy, hyEq⟩
    have hyv : y = rho.toOperator v := U.toLinearEquiv.injective hyEq
    simpa [hyv] using hy
  · intro h w
    have hw : U.toLinearEquiv (rho.toOperator (U.toLinearEquiv.symm w)) ∈
        C.carrier.map U.toLinearEquiv.toLinearMap :=
      ⟨rho.toOperator (U.toLinearEquiv.symm w), h (U.toLinearEquiv.symm w), rfl⟩
    simpa [QuantumCode.transport, UnitaryTransport.conjDensity,
      UnitaryTransport.conjOperator_apply] using hw
