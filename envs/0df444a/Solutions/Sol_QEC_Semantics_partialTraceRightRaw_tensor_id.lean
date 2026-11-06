-- Prove2me | solution 1 for QEC.Semantics.partialTraceRightRaw_tensor_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:33:17.491375+00:00
-- url     : https://prove2.me/submissions/50904ee8-61ec-47b4-80c7-d3b1e0a3a495

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
private theorem tensorRight_adjoint_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (k k' : K) (h : H) :
    LinearMap.adjoint (tensorRight H K k) (h ⊗ₜ[Complex] k') =
      (inner Complex k k') • h := by
  apply (ext_iff_inner_left Complex).mpr
  intro x
  rw [LinearMap.adjoint_inner_right]
  simp [tensorRight, TensorProduct.inner_tmul, inner_smul_right, mul_comm]
private theorem dual_apply_sum_stdOrthonormalBasis (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (ψ : Module.Dual Complex K) (k : K) :
    (∑ i : Fin (Module.finrank Complex K),
        ψ ((stdOrthonormalBasis Complex K) i) *
          inner Complex ((stdOrthonormalBasis Complex K) i) k) =
      ψ k := by
  let bK := stdOrthonormalBasis Complex K
  calc
    (∑ i : Fin (Module.finrank Complex K), ψ (bK i) * inner Complex (bK i) k)
        = ∑ i : Fin (Module.finrank Complex K), ψ (inner Complex (bK i) k • bK i) := by
          simp [bK, map_smul, mul_comm]
    _ = ψ (∑ i : Fin (Module.finrank Complex K), inner Complex (bK i) k • bK i) := by
          simp [map_sum]
    _ = ψ k := by
          rw [OrthonormalBasis.sum_repr']
private theorem partialTraceRightRaw_split_eq_compression_split (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    ((dualTensorHomEquiv Complex H H).toLinearMap.comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap)))
      =
    (partialTraceRightCompression H K).comp
      ((dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)).toLinearMap.comp
        (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
          (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap) := by
  apply TensorProduct.ext
  ext φ ψ h k z
  simp [partialTraceRightCompression, tensorRight_adjoint_tmul, LinearMap.comp_apply,
    dualTensorHomEquiv, dualTensorHom_apply]
  rw [← dual_apply_sum_stdOrthonormalBasis H K ψ k]
  simp [tensorRight, Finset.mul_sum, Finset.sum_smul, mul_comm, mul_assoc, smul_smul]
private theorem partialTraceRightRaw_eq_compression (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    partialTraceRightRaw H K = partialTraceRightCompression H K := by
  apply LinearMap.ext
  intro A
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
  have h_split :=
    congrArg (fun f => f (splitMap x)) (partialTraceRightRaw_split_eq_compression_split H K)
  simpa [partialTraceRightRaw, eC, splitMap, LinearMap.comp_apply, TensorProduct.map_map] using h_split
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
    (A : Operator H) :
    (partialTraceRightRaw H K)
        (TensorProduct.map A (LinearMap.id : K →ₗ[Complex] K)) =
      (Module.finrank Complex K : Complex) • A := by
  rw [partialTraceRightRaw_eq_compression]
  ext h
  simp only [partialTraceRightCompression, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.coe_mk]
  change
    (∑ i : Fin (Module.finrank Complex K),
      LinearMap.adjoint
        (tensorRight H K ((stdOrthonormalBasis Complex K) i))
        (A h ⊗ₜ[Complex] (stdOrthonormalBasis Complex K) i)) =
      (Module.finrank Complex K : Complex) • A h
  simp [tensorRight_adjoint_tmul]
  rw [Nat.cast_smul_eq_nsmul]
end QEC.Semantics
