-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.mem_externalBoundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:33.603789+00:00
-- url     : https://prove2.me/submissions/8c738f79-8e06-44f6-aac3-bed758ba7fbc

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
    (region : Finset L.Site) (site : L.Site) :
    site ∈ M.externalBoundary region ↔
      site ∉ region ∧ ∃ check, M.supportCouples check region ∧ site ∈ M.support check := by
  rw [externalBoundary, Finset.mem_sdiff, M.mem_boundary_iff]
  constructor
  · rintro ⟨⟨check, hcouples, hsite⟩, hnotmem⟩
    exact ⟨hnotmem, check, hcouples, hsite⟩
  · rintro ⟨hnotmem, check, hcouples, hsite⟩
    exact ⟨⟨check, hcouples, hsite⟩, hnotmem⟩
end QEC.Bounds.BPTCommutingProjectorModel
