-- Prove2me | solution 1 for QEC.Semantics.partialTraceRightRaw_trace_preserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:32:45.839383+00:00
-- url     : https://prove2.me/submissions/fdafcc60-bcb0-4bfa-95d6-2ed95d882618

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
section
universe u
namespace QEC
namespace Semantics
open scoped TensorProduct ComplexOrder
example (H : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : Operator H = Module.End Complex H := rfl
noncomputable example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (A : Operator H) : Complex :=
  LinearMap.trace Complex H A
example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (A : Operator H) : Prop :=
  LinearMap.IsPositive A
namespace DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
example : DensityOperator H → Operator H := fun rho => rho
end DensityOperator
namespace PositiveTracePreservingMap
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
noncomputable example {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] : PositiveTracePreservingMap H K → Operator H → Operator K :=
  fun Φ => Φ
end PositiveTracePreservingMap
namespace OperatorMatrix
variable {n : Nat} {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
end OperatorMatrix
namespace QuantumChannel
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
noncomputable example {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] : QuantumChannel H K → Operator H → Operator K :=
  fun Φ => Φ
end QuantumChannel
private theorem partialTraceRightRaw_contract_split (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    (contractLeft Complex H).comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap))
      =
    (contractLeft Complex (CompositeSystem H K)).comp
      (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
        (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap := by
  apply TensorProduct.ext
  ext φ ψ h k
  simp [mul_comm]
namespace PartialTraceRight
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
end PartialTraceRight
namespace QuantumCode
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
end QuantumCode
namespace DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
end DensityOperator
namespace UnitaryTransport
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
end UnitaryTransport
namespace QuantumCode
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
end QuantumCode
namespace DensityOperator
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
end DensityOperator
end Semantics
end QEC
end

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
namespace QEC.Semantics
theorem _root_.solution (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator (CompositeSystem H K)) :
    LinearMap.trace Complex H ((partialTraceRightRaw H K) A) =
      LinearMap.trace Complex (CompositeSystem H K) A := by
  let eC := dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)
  let x := eC.symm A
  have hA : A = eC x := by
    simp [x, eC]
  rw [hA]
  let splitMap :
      (Module.Dual Complex (CompositeSystem H K) ⊗[Complex] CompositeSystem H K) →ₗ[Complex]
        ((Module.Dual Complex H ⊗[Complex] Module.Dual Complex K) ⊗[Complex]
          (H ⊗[Complex] K)) :=
    TensorProduct.map (TensorProduct.dualDistribEquiv Complex H K).symm.toLinearMap
      (LinearMap.id : CompositeSystem H K →ₗ[Complex] CompositeSystem H K)
  have h_contract :=
    congrArg (fun f => f (splitMap x)) (partialTraceRightRaw_contract_split H K)
  simpa [partialTraceRightRaw, eC, splitMap, LinearMap.trace_eq_contract_apply,
    LinearMap.comp_apply, TensorProduct.map_map] using h_contract
end QEC.Semantics
