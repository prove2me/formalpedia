-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:58:36.800019+00:00
-- url     : https://prove2.me/submissions/19614370-0152-44ae-9002-98c6ba6a26de

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProductOn_isSymmetricProjection

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
theorem _root_.solution (M : BPTCommutingProjectorModel L kappa)
    (region : Finset L.Site) : (M.projectorAB region).IsSymmetricProjection :=
  M.projectorProductOn_isSymmetricProjection (M.interiorChecks region)
end QEC.Bounds.BPTCommutingProjectorModel
