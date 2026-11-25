-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThreeFam_span_21c22d7a9007
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:20:05.524281+00:00
-- url     : https://prove2.me/submissions/100e3dc2-b94b-4744-ba6b-6dd95586d38b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThreeSec_mem_8f4fbee0788e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThreeFam_linearIndependent_5353412cd3cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_coeffMap_injective_10b535f2daa8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution : Submodule.span ℂ (Set.range thetaThreeFam) = thetaThreeSpace := by
  have : Module.Finite ℂ thetaThreeSpace := Module.Finite.of_injective coeffMap coeffMap_injective
  have hle : Module.finrank ℂ thetaThreeSpace ≤ 3 := by
    simpa using LinearMap.finrank_le_finrank_of_injective coeffMap_injective
  let y : Fin (2 + 1) → thetaThreeSpace := fun ν => ⟨thetaThreeFam ν, thetaThreeSec_mem ν⟩
  have hy : LinearIndependent ℂ y :=
    LinearIndependent.of_comp thetaThreeSpace.subtype thetaThreeFam_linearIndependent
  have hcard : Fintype.card (Fin (2 + 1)) = Module.finrank ℂ thetaThreeSpace :=
    le_antisymm hy.fintype_card_le_finrank (by simpa using hle)
  have hspan := hy.span_eq_top_of_card_eq_finrank' hcard
  have hr : Set.range thetaThreeFam = thetaThreeSpace.subtype '' Set.range y := by
    rw [← Set.range_comp]; rfl
  rw [hr, Submodule.span_image, hspan, Submodule.map_subtype_top]
end GroundTheory.Heights₂.Heights.KeyFormula
