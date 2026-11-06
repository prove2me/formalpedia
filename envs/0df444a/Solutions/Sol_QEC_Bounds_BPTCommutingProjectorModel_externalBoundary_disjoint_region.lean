-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_disjoint_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:09:03.991058+00:00
-- url     : https://prove2.me/submissions/902033d7-8f1b-4cec-b7af-ec08d633ddb3

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
    (region : Finset L.Site) : Disjoint (M.externalBoundary region) region := by
  rw [Finset.disjoint_left]
  intro site hboundary hregion
  exact (Finset.mem_sdiff.mp hboundary).2 hregion
end QEC.Bounds.BPTCommutingProjectorModel
