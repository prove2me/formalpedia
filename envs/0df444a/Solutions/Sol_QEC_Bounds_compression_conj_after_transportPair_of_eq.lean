-- Prove2me | solution 1 for QEC.Bounds.compression_conj_after_transportPair_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:37.610477+00:00
-- url     : https://prove2.me/submissions/9421fe94-d075-4ba6-ae43-718b47910058

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
import Theorems.Thm_QEC_Bounds_compression_conj_after_transportPair

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v
namespace QEC.Bounds
theorem _root_.solution
    {S T H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (outer : Semantics.UnitaryTransport H K) (coordinates : Semantics.UnitaryTransport H T)
    (embedding : S →ₗ[Complex] T) (outputEmbedding : S →ₗ[Complex] K)
    (P : Semantics.Operator H)
    (houtput : outputEmbedding = outer.toLinearEquiv.toLinearMap.comp
      (coordinates.symm.toLinearEquiv.toLinearMap.comp embedding)) :
    (LinearMap.adjoint outputEmbedding).comp ((outer.conjOperator P).comp outputEmbedding) =
      (LinearMap.adjoint embedding).comp ((coordinates.conjOperator P).comp embedding) := by
  rw [houtput]
  exact compression_conj_after_transportPair outer coordinates embedding P
end QEC.Bounds
