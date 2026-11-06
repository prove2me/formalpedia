-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_BbarM_jointEigenspaces_isInternal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:04:41.114197+00:00
-- url     : https://prove2.me/submissions/f2d51931-eec5-4d81-8b9f-55120f9bb2b9

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_mul_CD_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_commute_projectorBC_mul_CD

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
      Module.End.eigenspace (M.projectorAB region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorBC region * M.projectorCD region) eigenvalue.1) := by
  apply LinearMap.IsSymmetric.directSum_isInternal_of_commute
    (M.projectorAB_isSymmetricProjection region).isSymmetric
    (M.projectorBC_mul_CD_isSymmetricProjection region).isSymmetric
  exact M.projectorAB_commute_projectorBC_mul_CD region
end QEC.Bounds.BPTCommutingProjectorModel
