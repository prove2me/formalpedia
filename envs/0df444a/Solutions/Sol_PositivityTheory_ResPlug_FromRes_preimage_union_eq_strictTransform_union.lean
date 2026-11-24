-- Prove2me | solution 1 for PositivityTheory.ResPlug.FromRes.preimage_union_eq_strictTransform_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:09:57.496618+00:00
-- url     : https://prove2.me/submissions/f53ff720-677e-48f9-a3cb-f3eca2f4459b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsClopen
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResSnc
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_strictTransform_eq_closure_preimage


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open PositivityTheory PositivityTheory.ResPlug PositivityTheory.ResPlug.FromRes
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace PositivityTheory.ResPlug.FromRes
theorem _root_.solution {X X₁ : Scheme.{0}} [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    π.base ⁻¹' (D.support : Set X) ∪ π.base ⁻¹' (Z.support : Set X) =
      ((FunctorialResolution.strictTransform π Z D).support : Set X₁) ∪ π.base ⁻¹' (Z.support : Set X) := by
  have e : FunctorialResolution.strictTransform π Z D = Blowup.strictTransform π Z D := rfl
  have hcl : ((FunctorialResolution.strictTransform π Z D).support : Set X₁) =
      closure (π.base ⁻¹' ((D.support : Set X) \ (Z.support : Set X))) := by
    rw [e]; exact support_strictTransform_eq_closure_preimage π Z D
  have hD : IsClosed (π.base ⁻¹' (D.support : Set X)) :=
    D.support.isClosed.preimage π.base.hom.continuous
  ext x
  constructor
  · rintro (hx | hx)
    · by_cases hz : x ∈ π.base ⁻¹' (Z.support : Set X)
      · exact Or.inr hz
      · left; rw [hcl]; exact subset_closure ⟨hx, hz⟩
    · exact Or.inr hx
  · rintro (hx | hx)
    · left
      rw [hcl] at hx
      exact closure_minimal (fun y hy => hy.1) hD hx
    · exact Or.inr hx
end PositivityTheory.ResPlug.FromRes
