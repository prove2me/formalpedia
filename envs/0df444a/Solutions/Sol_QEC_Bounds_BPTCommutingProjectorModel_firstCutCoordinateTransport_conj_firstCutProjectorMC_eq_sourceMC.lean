-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:49:46.330768+00:00
-- url     : https://prove2.me/submissions/c70c00b2-9c1c-4ac6-b4ff-71fa73508d05

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorAB
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorBC
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) =
      (M.fourFactorTransport region).conjOperator
        (M.projectorAB region * M.projectorBC region) := by
  calc
    (M.firstCutCoordinateTransport region).conjOperator
        (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) =
        M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) :=
      M.firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC region
    _ = (M.fourFactorTransport region).conjOperator (M.projectorAB region) *
          (M.fourFactorTransport region).conjOperator (M.projectorBC region) := by
      exact (congrArg₂ (· * ·)
        (M.fourFactorTransport_conj_projectorAB region)
        (M.fourFactorTransport_conj_projectorBC region)).symm
    _ = (M.fourFactorTransport region).conjOperator
          (M.projectorAB region * M.projectorBC region) :=
      (Semantics.UnitaryTransport.conjOperator_mul
        (M.fourFactorTransport region) (M.projectorAB region) (M.projectorBC region)).symm
end QEC.Bounds.BPTCommutingProjectorModel
