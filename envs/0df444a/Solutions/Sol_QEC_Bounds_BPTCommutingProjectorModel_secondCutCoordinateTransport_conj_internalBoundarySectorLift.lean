-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_internalBoundarySectorLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:59:56.879202+00:00
-- url     : https://prove2.me/submissions/6c7d31e8-b7b0-48f9-892a-cc8ad4483a1e

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap


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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region)))) := by
  unfold secondCutCoordinateTransport overlapLiftLeft
  rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
        (1 : Semantics.Operator (M.fourFactorD region)) by
      symm
      exact TensorProduct.map_one]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator (M.fourFactorA region)) Z
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
      (1 : Semantics.Operator (M.fourFactorD region)))
end QEC.Bounds.BPTCommutingProjectorModel
