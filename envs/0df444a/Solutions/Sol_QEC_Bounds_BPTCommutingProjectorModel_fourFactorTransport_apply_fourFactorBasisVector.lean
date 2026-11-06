-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_apply_fourFactorBasisVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:51:08.928528+00:00
-- url     : https://prove2.me/submissions/5b2b7b75-a194-47d0-8f2f-d1b38c5a77a0

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_apply_basis

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
    (labels : Semantics.Qudit.Label L.localDimension) :
    M.fourFactorTransport region
        (EuclideanSpace.basisFun (Semantics.Qudit.Label L.localDimension) Complex labels) =
      M.fourFactorBasisVector region labels := by
  unfold fourFactorBasisVector
  exact M.fourFactorTransport_apply_basis region labels
end QEC.Bounds.BPTCommutingProjectorModel
