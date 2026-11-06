-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorBCLocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:53:19.992216+00:00
-- url     : https://prove2.me/submissions/ba8ce960-ba6e-4118-b737-3622a5fc11c5

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor

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
    (M.regionSubsystem (M.boundary region)).extendLocalToRegister (M.projectorBCLocal region) =
      M.projectorBC region :=
  Classical.choose_spec (M.projectorBC_supportedOnRegister_boundary region)
end QEC.Bounds.BPTCommutingProjectorModel
