-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_tensorMap_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:08:00.128007+00:00
-- url     : https://prove2.me/submissions/fa66b291-ddc6-4685-9c7c-5b16f1fd7930

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_InternalResidual
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ExternalLocal
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryLTensor_conj_tensorMap_left
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap_right


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
    (Z : Semantics.Operator C) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H)) Z) =
      TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
        (TensorProduct.map (1 : Semantics.Operator N) Z) := by
  unfold isotypicSectorBlockTransportLeft
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [unitaryRTensor_conj_tensorMap_right (unitaryLTensor A U) C Z]
  rw [show (1 : Semantics.Operator (Semantics.CompositeSystem A
      (Semantics.CompositeSystem W N))) =
      TensorProduct.map (1 : Semantics.Operator A)
        (1 : Semantics.Operator (Semantics.CompositeSystem W N)) by
      symm
      exact TensorProduct.map_one]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [unitaryLTensor_conj_tensorMap_left]
  rw [show (1 : Semantics.Operator (Semantics.CompositeSystem W N)) =
      TensorProduct.map (1 : Semantics.Operator W) (1 : Semantics.Operator N) by
      symm
      exact TensorProduct.map_one]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [tensorAssociatorUnitary_symm_conj_tensorMap]
  rw [show TensorProduct.map (1 : Semantics.Operator A) (1 : Semantics.Operator W) =
      (1 : Semantics.Operator (Semantics.CompositeSystem A W)) from TensorProduct.map_one]
end QEC.Bounds.BPTCommutingProjectorModel
