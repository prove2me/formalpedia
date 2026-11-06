-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:01:10.057322+00:00
-- url     : https://prove2.me/submissions/e7e12a91-5fa3-44c8-926c-f18e1b35fd75

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_commute_projectorBC
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
    (M.projectorAB region * M.projectorBC region).IsSymmetricProjection :=
  isSymmetricProjection_mul_of_commute
    (M.projectorAB_isSymmetricProjection region)
    (M.projectorBC_isSymmetricProjection region)
    (M.projectorAB_commute_projectorBC region)
end QEC.Bounds.BPTCommutingProjectorModel
