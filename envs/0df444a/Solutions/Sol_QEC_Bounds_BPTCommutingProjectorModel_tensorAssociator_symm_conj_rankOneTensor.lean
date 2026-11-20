-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tensorAssociator_symm_conj_rankOneTensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:27:48.131501+00:00
-- url     : https://prove2.me/submissions/e69d84c2-2aac-4c5a-983d-6ff588eb28ea

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_conj_tensorMap


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H K J : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K] [NormedAddCommGroup J] [InnerProductSpace Complex J]
    [Semantics.FiniteQuantumSystem J]
    (phi : H) (chi : K) (Q : Semantics.Operator J) :
    (tensorAssociatorUnitary H K J).symm.conjOperator
      (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap
        (TensorProduct.map (InnerProductSpace.rankOne Complex chi chi).toLinearMap Q)) =
      TensorProduct.map
        (InnerProductSpace.rankOne Complex (phi ⊗ₜ[Complex] chi)
          (phi ⊗ₜ[Complex] chi)).toLinearMap Q := by
  rw [tensorAssociatorUnitary_symm_conj_tensorMap]
  rw [Semantics.DensityOperator.tensorMap_rankOne]
end QEC.Bounds.BPTCommutingProjectorModel
