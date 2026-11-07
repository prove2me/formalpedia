-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:20.244256+00:00
-- url     : https://prove2.me/submissions/0af4d2e9-d392-4e9e-89aa-af30e3fd787e

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_apply_basis_eq_fourFactorTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_ext


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
    M.boundaryGlobalToFourFactorTransport region = M.fourFactorTransport region := by
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  exact M.boundaryGlobalToFourFactorTransport_apply_basis_eq_fourFactorTransport region labels
end QEC.Bounds.BPTCommutingProjectorModel
