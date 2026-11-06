-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.extendLocalToRegister_projectorCDLocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:53:31.744973+00:00
-- url     : https://prove2.me/submissions/164869f4-de65-4f0e-b0de-59443059e64f

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
    (M.regionSubsystem regionᶜ).extendLocalToRegister (M.projectorCDLocal region) =
      M.projectorCD region :=
  Classical.choose_spec (M.projectorCD_supportedOnRegister_complement region)
end QEC.Bounds.BPTCommutingProjectorModel
