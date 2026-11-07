-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_BbarM_eq_sourceBC_mul_CD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:49:58.621801+00:00
-- url     : https://prove2.me/submissions/afcb4a63-75f6-4ccd-bac3-45cfadc35ee3

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_overlapLiftRight_BbarM
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorBC
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorCD


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
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftRight (A := M.fourFactorA region)
        (M.secondCutProjectorBbarM region)) =
      (M.fourFactorTransport region).conjOperator
        (M.projectorBC region * M.projectorCD region) := by
  calc
    (M.secondCutCoordinateTransport region).conjOperator
        (overlapLiftRight (A := M.fourFactorA region)
          (M.secondCutProjectorBbarM region)) =
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) :=
      M.secondCutCoordinateTransport_conj_overlapLiftRight_BbarM region
    _ = (M.fourFactorTransport region).conjOperator (M.projectorBC region) *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
      exact (congrArg₂ (· * ·)
        (M.fourFactorTransport_conj_projectorBC region)
        (M.fourFactorTransport_conj_projectorCD region)).symm
    _ = (M.fourFactorTransport region).conjOperator
          (M.projectorBC region * M.projectorCD region) :=
      (Semantics.UnitaryTransport.conjOperator_mul
        (M.fourFactorTransport region) (M.projectorBC region) (M.projectorCD region)).symm
end QEC.Bounds.BPTCommutingProjectorModel
