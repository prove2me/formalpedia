-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:34:38.926892+00:00
-- url     : https://prove2.me/submissions/3ad6fa29-4e9e-4e01-b5a6-070ac5b4fafb

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
theorem _root_.solution (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) : (M.regionSubsystem region).selected = region :=
  L.subsystem_selected region
end QEC.Bounds.BPTCommutingProjectorModel
