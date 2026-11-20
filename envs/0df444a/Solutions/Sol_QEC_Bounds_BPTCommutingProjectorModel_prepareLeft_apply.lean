-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.prepareLeft_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:59.198543+00:00
-- url     : https://prove2.me/submissions/349208e4-69ba-43ef-b298-9fdaeaa1aa9e

import Definitions.Def_QEC_Bounds_BPTDisentangling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_prepareLeft_apply_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_tensorMap_sum_left_reference
import Theorems.Thm_QEC_Semantics_QuditSubsystem_tensorMap_sum_right_reference


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (A : Operator K) :
    prepareLeft H K rho A = TensorProduct.map rho.toOperator A := by
  let basis := stdOrthonormalBasis Complex K
  rw [Semantics.QuditSubsystem.operator_eq_sum_rankOne_basis K basis A]
  rw [map_sum]
  rw [Semantics.QuditSubsystem.tensorMap_sum_right_reference]
  apply Finset.sum_congr rfl
  intro i _
  rw [prepareLeft_apply_rankOne]
  calc
    (∑ j,
      (InnerProductSpace.rankOne Complex
        (densityEnsembleVectors H rho j ⊗ₜ[Complex] (A (basis i)))
        (densityEnsembleVectors H rho j ⊗ₜ[Complex] (basis i))).toLinearMap) =
        ∑ j, TensorProduct.map
          (InnerProductSpace.rankOne Complex (densityEnsembleVectors H rho j)
            (densityEnsembleVectors H rho j)).toLinearMap
          (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
            apply Finset.sum_congr rfl
            intro j _
            rw [tensorMap_rankOne]
    _ = TensorProduct.map (∑ j,
        (InnerProductSpace.rankOne Complex (densityEnsembleVectors H rho j)
          (densityEnsembleVectors H rho j)).toLinearMap)
        (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
          rw [Semantics.QuditSubsystem.tensorMap_sum_left_reference]
    _ = TensorProduct.map rho.toOperator
        (InnerProductSpace.rankOne Complex (A (basis i)) (basis i)).toLinearMap := by
          rw [← densityEnsemble_specification]
end QEC.Bounds.BPTCommutingProjectorModel
