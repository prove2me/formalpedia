-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:34:42.556652+00:00
-- url     : https://prove2.me/submissions/5b483034-0aaf-4b6d-97e7-280f4e8aae6f

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
    (region : Finset L.Site) (site : L.Site) :
    site ∈ (M.regionSubsystem region).selected ↔ site ∈ region :=
  L.mem_subsystem_selected_iff region site
end QEC.Bounds.BPTCommutingProjectorModel
