-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlapLiftLeft_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:06:56.647698+00:00
-- url     : https://prove2.me/submissions/76dad196-e3bc-480b-9e2a-d7e59c26f57f

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOneTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryLTensor_conj_tensorMap_left
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap_left


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (E : Semantics.Operator (Semantics.CompositeSystem A H))
    (X : Semantics.Operator N)
    (hE : (unitaryLTensor A U).conjOperator E =
      TensorProduct.map (1 : Semantics.Operator A)
        (TensorProduct.map (1 : Semantics.Operator W) X)) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftLeft (C := C) E) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
        (TensorProduct.map X (1 : Semantics.Operator C)) := by
  unfold isotypicSectorBlockTransportLeft overlapLiftLeft
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [unitaryRTensor_conj_tensorMap_left, hE]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [unitaryLTensor_conj_tensorMap_left]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [tensorAssociatorUnitary_symm_conj_tensorMap]
  rw [show TensorProduct.map (1 : Semantics.Operator A)
      (1 : Semantics.Operator W) =
        (1 : Semantics.Operator (Semantics.CompositeSystem A W)) from TensorProduct.map_one]
end QEC.Bounds.BPTCommutingProjectorModel
