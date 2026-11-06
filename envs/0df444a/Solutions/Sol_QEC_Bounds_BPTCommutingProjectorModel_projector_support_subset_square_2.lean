-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.projector_support_subset_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:53:51.560209+00:00
-- url     : https://prove2.me/submissions/e781209e-1bc9-4f65-b2dc-d3a256f0db5c

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution (M : BPTCommutingProjectorModel L κ) (check : κ) :
    M.support check ⊆ L.lattice.square (M.squareOrigin check) M.interactionRange :=
  M.support_subset_square check
end QEC.Bounds.BPTCommutingProjectorModel
