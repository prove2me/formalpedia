-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundaryComplementToADTransport_apply_boundaryComplementToADBasisVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:53:30.722207+00:00
-- url     : https://prove2.me/submissions/d049cdf9-4e9e-4521-8d46-13e08c740788

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryComplementToADTransport_toLinearEquiv_apply_basis

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
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (M.boundary region)).complementDimensions) :
    (M.boundaryComplementToADTransport region).toLinearEquiv
        (EuclideanSpace.basisFun
          (Semantics.Qudit.Label
            (M.regionSubsystem (M.boundary region)).complementDimensions) Complex labels) =
      M.boundaryComplementToADBasisVector region labels := by
  unfold boundaryComplementToADBasisVector
  exact M.boundaryComplementToADTransport_toLinearEquiv_apply_basis region labels
end QEC.Bounds.BPTCommutingProjectorModel
