-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorBC_commute_projectorCD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:24:35.510395+00:00
-- url     : https://prove2.me/submissions/f0999101-7153-44f8-b3ca-60f5178b07c3

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
    (region : Finset L.Site) : Commute (M.projectorBC region) (M.projectorCD region) :=
  M.projectorProductOn_commute (M.boundaryChecks region) (M.exteriorChecks region)
end QEC.Bounds.BPTCommutingProjectorModel
