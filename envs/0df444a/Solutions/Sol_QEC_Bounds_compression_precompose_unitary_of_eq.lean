-- Prove2me | solution 1 for QEC.Bounds.compression_precompose_unitary_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:53:08.111428+00:00
-- url     : https://prove2.me/submissions/fbed7e57-fb4b-4ada-92af-25612b71d490

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_precompose_unitary


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
namespace QEC.Bounds
theorem _root_.solution
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport S H) (J : H →ₗ[Complex] K)
    (Jnew : S →ₗ[Complex] K) (hJnew : Jnew = J.comp U.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator K) :
    (LinearMap.adjoint Jnew).comp (P.comp Jnew) =
      U.symm.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by
  rw [hJnew]
  exact BPTCommutingProjectorModel.compression_precompose_unitary U J P
end QEC.Bounds
