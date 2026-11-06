-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_conj_overlapLiftLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:05:43.876419+00:00
-- url     : https://prove2.me/submissions/dc6a7992-fe76-461a-92c9-095f86f59ce3

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Conjugation
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_associator_coherence
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
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
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (hleft : (unitaryLTensor A U).conjOperator P =
      rightTensorExtensionAfterLeft A W N Pleft) :
    (isotypicSectorBlockTransportLeft A H W N C U).conjOperator
        (overlapLiftLeft (C := C) P) =
      TensorProduct.map Pleft
        (1 : Semantics.Operator (Semantics.CompositeSystem N C)) := by
  unfold isotypicSectorBlockTransportLeft
  rw [composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  unfold overlapLiftLeft
  rw [unitaryRTensor_conj_tensorMap_left, hleft]
  unfold rightTensorExtensionAfterLeft
  rw [← unitaryRTensor_conj_tensorMap_left
    (tensorAssociatorUnitary A W N) C
    (TensorProduct.map Pleft (1 : Semantics.Operator N))]
  rw [← composeUnitaryTransport_conjOperator
    (unitaryRTensor (tensorAssociatorUnitary A W N) C)
    (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C)]
  rw [← composeUnitaryTransport_conjOperator
    (composeUnitaryTransport
      (unitaryRTensor (tensorAssociatorUnitary A W N) C)
      (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C))
    (unitaryLTensor A (tensorAssociatorUnitary W N C))]
  rw [← composeUnitaryTransport_conjOperator
    (composeUnitaryTransport
      (composeUnitaryTransport
        (unitaryRTensor (tensorAssociatorUnitary A W N) C)
        (tensorAssociatorUnitary A (Semantics.CompositeSystem W N) C))
      (unitaryLTensor A (tensorAssociatorUnitary W N C)))
    (tensorAssociatorUnitary A W (Semantics.CompositeSystem N C)).symm]
  rw [isotypicSectorBlockTransportLeft_associator_coherence]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [show TensorProduct.map (1 : Semantics.Operator N)
      (1 : Semantics.Operator C) =
        (1 : Semantics.Operator (Semantics.CompositeSystem N C)) from
      TensorProduct.map_one]
end QEC.Bounds.BPTCommutingProjectorModel
