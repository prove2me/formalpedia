-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.regionErasureChannel_specification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:54:49.551006+00:00
-- url     : https://prove2.me/submissions/98a68b26-bf55-4d80-9bdf-19e73a86bdf6

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
    (region : Finset L.Site) :
    M.regionErasureChannel region = (M.regionSubsystem region).erasureChannelFromRegister :=
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
