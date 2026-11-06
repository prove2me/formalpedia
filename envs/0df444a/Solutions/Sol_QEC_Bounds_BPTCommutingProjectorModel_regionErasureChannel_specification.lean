-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.regionErasureChannel_specification
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:51:36.633206+00:00
-- url     : https://prove2.me/submissions/573763d3-da2e-49de-921e-9317c40f42d1

-- ID: de0bb2fc-ca5a-45f9-a853-6c7d72851da7 | NAME: QEC.Bounds.BPTCommutingProjectorModel.regionErasureChannel_specification | 未本地编译验证
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

theorem solution (M : BPTCommutingProjectorModel L κ)
    (region : Finset L.Site) :
    M.regionErasureChannel region = (M.regionSubsystem region).erasureChannelFromRegister := by
  rfl
