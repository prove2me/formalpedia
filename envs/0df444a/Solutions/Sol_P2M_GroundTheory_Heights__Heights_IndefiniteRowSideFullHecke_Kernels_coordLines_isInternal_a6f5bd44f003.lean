-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_isInternal_a6f5bd44f003
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:53.530098+00:00
-- url     : https://prove2.me/submissions/64261454-26fb-4cc6-8cff-bf876e376903

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution (K : Type*) [Field K] : DirectSum.IsInternal (coordLines K) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)]
    rw [disjoint_iff_inf_le]
    rintro v ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    simp at h0 h1
    ext i; fin_cases i <;> simp [h0.symm]
  · exact LinearMap.iSup_range_single _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
