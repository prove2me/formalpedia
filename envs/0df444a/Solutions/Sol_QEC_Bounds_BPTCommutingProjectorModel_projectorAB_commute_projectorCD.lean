-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_commute_projectorCD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:24:34.733006+00:00
-- url     : https://prove2.me/submissions/2282a4ef-1f8b-40ab-a9b9-cb80b3cf6cd5

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProductOn_commute

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
    (region : Finset L.Site) : Commute (M.projectorAB region) (M.projectorCD region) :=
  M.projectorProductOn_commute (M.interiorChecks region) (M.exteriorChecks region)
end QEC.Bounds.BPTCommutingProjectorModel
