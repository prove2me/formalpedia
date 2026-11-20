-- Prove2me | solution 1 for QEC.Bounds.tensorAssociatorUnitary_symm_conj_leftMap_right_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:51:33.558773+00:00
-- url     : https://prove2.me/submissions/68890375-04a2-48ca-b61a-bedb3b21bbfb

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_conj_tensorMap


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
namespace QEC.Bounds
theorem _root_.solution
    {H K J : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup J] [InnerProductSpace Complex J] [Semantics.FiniteQuantumSystem J]
    (A : Semantics.Operator H) :
    (BPTCommutingProjectorModel.tensorAssociatorUnitary H K J).symm.conjOperator
        (TensorProduct.map A (1 : Semantics.Operator (Semantics.CompositeSystem K J))) =
      TensorProduct.map (TensorProduct.map A (1 : Semantics.Operator K))
        (1 : Semantics.Operator J) := by
  rw [show (1 : Semantics.Operator (Semantics.CompositeSystem K J)) =
      TensorProduct.map (1 : Semantics.Operator K) (1 : Semantics.Operator J) by
        symm
        exact TensorProduct.map_one]
  exact BPTCommutingProjectorModel.tensorAssociatorUnitary_symm_conj_tensorMap A
    (1 : Semantics.Operator K) (1 : Semantics.Operator J)
end QEC.Bounds
