-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RankFracDegree_proof_15a56f1b43bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:30.101622+00:00
-- url     : https://prove2.me/submissions/c7fc82d0-b8ce-4201-8e1c-2a6e0f54d7de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRankFracDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RankFracDegree_isFractionRing_of_closure_00df87cf7f7b

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace RankFracDegree
theorem _root_.solution : RankFracDegree.Statement := by
  intro F Ω A B _ _ _ _ _ _ L₀ L f g hf hg hfg hfL₀ hgL hL₀ hL _
  have hle : L₀ ≤ L := by
    intro x hx
    have h1 : x ∈ Subfield.closure (Set.range g) := by
      refine Subfield.closure_mono ?_ (hL₀ hx)
      rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap A B a, hfg a⟩
    exact (Subfield.closure_le (t := L.toSubfield)).mpr (by rintro _ ⟨b, rfl⟩; exact hgL b) h1
  let L' := IntermediateField.extendScalars hle
  let _ : Algebra A L₀ := (f.codRestrict L₀ hfL₀).toAlgebra
  let _ : Algebra B L' := (g.codRestrict L' hgL).toAlgebra
  let _ : Algebra A L' := ((algebraMap L₀ L').comp (algebraMap A L₀)).toAlgebra
  have _ : IsScalarTower A L₀ L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower A B L' := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hfg a).symm
  have _ : IsFractionRing A L₀ := RankFracDegree.isFractionRing_of_closure L₀ f hf hfL₀ hL₀
  have _ : IsFractionRing B L' := RankFracDegree.isFractionRing_of_closure L' g hg hgL hL
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact (IsFractionRing.finrank_eq A L₀ B L').symm
end RankFracDegree
end GroundTheory.Heights₂.Heights.Inter
