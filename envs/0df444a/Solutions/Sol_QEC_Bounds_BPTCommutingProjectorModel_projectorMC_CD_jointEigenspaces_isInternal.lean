-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorMC_CD_jointEigenspaces_isInternal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:04:35.545904+00:00
-- url     : https://prove2.me/submissions/471b3d47-a00f-42bd-b6e1-c222efb97bbf

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorCD_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_mul_BC_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_mul_BC_commute_projectorCD

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
    DirectSum.IsInternal (fun eigenvalue : Complex × Complex =>
      Module.End.eigenspace (M.projectorAB region * M.projectorBC region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorCD region) eigenvalue.1) := by
  apply LinearMap.IsSymmetric.directSum_isInternal_of_commute
    (M.projectorAB_mul_BC_isSymmetricProjection region).isSymmetric
    (M.projectorCD_isSymmetricProjection region).isSymmetric
  exact M.projectorAB_mul_BC_commute_projectorCD region
end QEC.Bounds.BPTCommutingProjectorModel
