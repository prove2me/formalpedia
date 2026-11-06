-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.sum_code_basis_eq_projector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:27:01.694037+00:00
-- url     : https://prove2.me/submissions/2428358d-8b63-4cc3-9ef0-6160d6b51995

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Semantics_DensityOperator_comp_adjoint_eq_sum_rankOne


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
namespace QEC.Bounds.BPTEntropy
theorem _root_.solution {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) :
    ∑ i : Fin C.dimension,
      (InnerProductSpace.rankOne Complex
        ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
        ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)).toLinearMap =
      C.projector := by
  let b : OrthonormalBasis (Fin C.dimension) Complex C.carrier :=
    stdOrthonormalBasis Complex C.carrier
  let inclusion : C.carrier →ₗ[Complex] H := C.carrier.subtypeₗᵢ.toLinearMap
  have hAdj : LinearMap.adjoint inclusion = C.carrier.orthogonalProjection.toLinearMap := by
    apply LinearMap.ext
    intro x
    change (LinearMap.toContinuousLinearMap (LinearMap.adjoint inclusion)) x =
      C.carrier.orthogonalProjection x
    rw [LinearMap.adjoint_toContinuousLinearMap]
    change (ContinuousLinearMap.adjoint C.carrier.subtypeL) x =
      C.carrier.orthogonalProjection x
    rw [C.carrier.adjoint_subtypeL]
  have hProj : inclusion.comp (LinearMap.adjoint inclusion) = C.projector := by
    rw [hAdj]
    ext x
    rfl
  calc
    ∑ i : Fin C.dimension,
        (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
          ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)).toLinearMap =
        ∑ i, (InnerProductSpace.rankOne Complex (inclusion (b i)) (inclusion (b i))).toLinearMap := by
          congr
    _ = inclusion.comp (LinearMap.adjoint inclusion) :=
      (comp_adjoint_eq_sum_rankOne b inclusion).symm
    _ = C.projector := hProj
end QEC.Bounds.BPTEntropy
