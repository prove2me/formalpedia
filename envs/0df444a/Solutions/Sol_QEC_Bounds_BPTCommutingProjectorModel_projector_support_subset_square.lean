-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projector_support_subset_square
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:53:12.329504+00:00
-- url     : https://prove2.me/submissions/4c583ef0-f399-41d9-bf72-a16cb47c1baf

-- ID: 2d2288ea-bdae-49ca-96e4-94ef391e6835 | NAME: QEC.Bounds.BPTCommutingProjectorModel.projector_support_subset_square | 未本地编译验证
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

theorem solution (M : BPTCommutingProjectorModel L κ) (check : κ) :
    M.support check ⊆ L.lattice.square (M.squareOrigin check) M.interactionRange := by
  exact M.support_subset_square check
