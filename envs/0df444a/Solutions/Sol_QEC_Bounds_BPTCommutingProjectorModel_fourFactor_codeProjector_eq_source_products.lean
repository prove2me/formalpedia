-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactor_codeProjector_eq_source_products
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:49:51.183827+00:00
-- url     : https://prove2.me/submissions/023ed8ce-e853-4799-8fb0-da3d6abc8a1d

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorAB
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorCD
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorBC
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_eq_projectorAB_mul_BC_mul_CD

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
    (M.fourFactorTransport region).conjOperator M.fullCodeProjector =
      (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
        M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
        M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
  rw [M.fullCodeProjector_eq_projectorAB_mul_BC_mul_CD]
  calc
    (M.fourFactorTransport region).conjOperator
        ((M.projectorAB region * M.projectorBC region) * M.projectorCD region) =
        (M.fourFactorTransport region).conjOperator
            (M.projectorAB region * M.projectorBC region) *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
      exact Semantics.UnitaryTransport.conjOperator_mul
        (M.fourFactorTransport region)
        (M.projectorAB region * M.projectorBC region) (M.projectorCD region)
    _ = ((M.fourFactorTransport region).conjOperator (M.projectorAB region) *
          (M.fourFactorTransport region).conjOperator (M.projectorBC region)) *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
      exact congrArg
        (fun product => product *
          (M.fourFactorTransport region).conjOperator (M.projectorCD region))
        (Semantics.UnitaryTransport.conjOperator_mul
          (M.fourFactorTransport region) (M.projectorAB region) (M.projectorBC region))
    _ = (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
      have hAB := M.fourFactorTransport_conj_projectorAB region
      have hBC := M.fourFactorTransport_conj_projectorBC region
      have hCD := M.fourFactorTransport_conj_projectorCD region
      exact congrArg₂ (fun left right => left * right)
        (congrArg₂ (fun left right => left * right) hAB hBC) hCD
end QEC.Bounds.BPTCommutingProjectorModel
