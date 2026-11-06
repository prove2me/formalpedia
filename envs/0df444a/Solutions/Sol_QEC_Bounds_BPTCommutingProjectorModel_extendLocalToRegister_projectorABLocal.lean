-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorABLocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:53:19.23511+00:00
-- url     : https://prove2.me/submissions/055de418-d54d-4dd5-bf4f-215b4ee8a20c

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
    (M.regionSubsystem region).extendLocalToRegister (M.projectorABLocal region) =
      M.projectorAB region :=
  Classical.choose_spec (M.projectorAB_supportedOnRegister_region region)
end QEC.Bounds.BPTCommutingProjectorModel
