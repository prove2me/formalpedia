-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorBC_mul_CD_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:02:16.000688+00:00
-- url     : https://prove2.me/submissions/ee523e57-9cf1-48ef-b66e-992184b18a19

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorCD_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_commute_projectorCD
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_mul_of_commute

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
    (M.projectorBC region * M.projectorCD region).IsSymmetricProjection :=
  isSymmetricProjection_mul_of_commute
    (M.projectorBC_isSymmetricProjection region)
    (M.projectorCD_isSymmetricProjection region)
    (M.projectorBC_commute_projectorCD region)
end QEC.Bounds.BPTCommutingProjectorModel
