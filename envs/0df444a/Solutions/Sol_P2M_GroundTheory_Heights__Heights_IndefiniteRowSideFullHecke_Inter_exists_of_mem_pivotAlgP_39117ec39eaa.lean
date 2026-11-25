-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_of_mem_pivotAlgP_39117ec39eaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:20.969572+00:00
-- url     : https://prove2.me/submissions/6e7eb880-1d76-4df2-8c1d-d205f372d87f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotAlgP_eq_map_0b609fa3b405

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {y : MvPolynomial (Fin n × Fin n) F} (hy : y ∈ pivotAlgP F n) :
    ∃ z : pivotAlg F n, ((z : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F) = y := by
  rw [pivotAlgP_eq_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨⟨z, hz⟩, rfl⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
