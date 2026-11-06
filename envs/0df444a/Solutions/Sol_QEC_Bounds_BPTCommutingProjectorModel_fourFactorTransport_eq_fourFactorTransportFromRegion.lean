-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_eq_fourFactorTransportFromRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:55:15.407706+00:00
-- url     : https://prove2.me/submissions/e4fd62a4-d354-4235-8bdf-acad992b7fd3

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_apply_basis
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransportFromRegion_apply_basis
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
    M.fourFactorTransport region = M.fourFactorTransportFromRegion region := by
  apply unitaryTransport_ext
  apply LinearEquiv.toLinearMap_injective
  apply (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex).toBasis.ext
  intro labels
  change M.fourFactorTransport region
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
    M.fourFactorTransportFromRegion region
      (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels)
  rw [M.fourFactorTransport_apply_basis, M.fourFactorTransportFromRegion_apply_basis]
end QEC.Bounds.BPTCommutingProjectorModel
