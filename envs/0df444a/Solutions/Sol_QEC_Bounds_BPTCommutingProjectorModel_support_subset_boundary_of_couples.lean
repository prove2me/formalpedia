-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.support_subset_boundary_of_couples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:09:03.0918+00:00
-- url     : https://prove2.me/submissions/84e4c8a4-6542-4665-885e-f2256f8d4b31

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_boundary_iff

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
    (region : Finset L.Site) (check : κ) (hcouples : M.supportCouples check region) :
    M.support check ⊆ M.boundary region := by
  intro site hsite
  exact M.mem_boundary_iff region site |>.2 ⟨check, hcouples, hsite⟩
end QEC.Bounds.BPTCommutingProjectorModel
