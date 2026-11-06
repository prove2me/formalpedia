-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_commute_projectorBC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:20:54.738783+00:00
-- url     : https://prove2.me/submissions/910b6aaa-97d0-40c3-ac5b-a291563e1907

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
    (region : Finset L.Site) : Commute (M.projectorAB region) (M.projectorBC region) :=
  M.projectorProductOn_commute (M.interiorChecks region) (M.boundaryChecks region)
end QEC.Bounds.BPTCommutingProjectorModel
