-- Prove2me | solution 1 for QEC.Bounds.embedding_compression_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:49:22.136101+00:00
-- url     : https://prove2.me/submissions/97f3fc96-0260-4df6-b935-adb920d9f2b2

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
namespace QEC.Bounds
theorem _root_.solution
    {S K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (E : S →ₗ[Complex] K) {P Q : Semantics.Operator K} (h : P = Q) :
    (LinearMap.adjoint E).comp (P.comp E) =
      (LinearMap.adjoint E).comp (Q.comp E) := by
  subst Q
  rfl
end QEC.Bounds
