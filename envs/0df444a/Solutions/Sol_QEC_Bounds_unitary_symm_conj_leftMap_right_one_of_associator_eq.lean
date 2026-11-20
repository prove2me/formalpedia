-- Prove2me | solution 1 for QEC.Bounds.unitary_symm_conj_leftMap_right_one_of_associator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:51.065175+00:00
-- url     : https://prove2.me/submissions/0a10cd33-b011-4c12-acf0-b9fa7872f971

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_RegionCompressionRaw
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Assembly_CompressionAlgebra
import Theorems.Thm_QEC_Bounds_tensorAssociatorUnitary_symm_conj_leftMap_right_one

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
    (O : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem H K) J)
      (Semantics.CompositeSystem H (Semantics.CompositeSystem K J)))
    (hO : O = BPTCommutingProjectorModel.tensorAssociatorUnitary H K J)
    (A : Semantics.Operator H) :
    O.symm.conjOperator
        (TensorProduct.map A (1 : Semantics.Operator (Semantics.CompositeSystem K J))) =
      TensorProduct.map (TensorProduct.map A (1 : Semantics.Operator K))
        (1 : Semantics.Operator J) := by
  rw [hO]
  exact tensorAssociatorUnitary_symm_conj_leftMap_right_one A
end QEC.Bounds
