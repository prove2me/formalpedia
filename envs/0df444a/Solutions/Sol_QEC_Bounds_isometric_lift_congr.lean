-- Prove2me | solution 1 for QEC.Bounds.isometric_lift_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:53:12.17029+00:00
-- url     : https://prove2.me/submissions/5cc0a4f2-2e84-4c8a-b54a-706d7e46e202

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
    (E : S →ₗ[Complex] K) {P Q : Semantics.Operator S} (h : P = Q) :
    E.comp (P.comp (LinearMap.adjoint E)) =
      E.comp (Q.comp (LinearMap.adjoint E)) := by
  subst Q
  rfl
end QEC.Bounds
