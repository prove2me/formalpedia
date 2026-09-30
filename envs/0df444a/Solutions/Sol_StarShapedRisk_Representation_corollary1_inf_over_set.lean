-- Prove2me | solution 1 for StarShapedRisk.Representation.corollary1_inf_over_set
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:39.77352+00:00
-- url     : https://prove2.me/submissions/dd4467b3-f303-4cb1-9a49-c5ca599de731

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
set_option autoImplicit false
open StarShapedRisk.Representation
theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsStarShapedRiskMeasure 𝒳 ρ) (Γ : Set (𝒳.carrier → ℝ))
    (hΓ : ∀ γ ∈ Γ, IsConvexRiskMeasure 𝒳 γ)
    (h11 : ∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ) (ρ X)) (𝒴 : Set 𝒳.carrier) :
    ⨅ X ∈ 𝒴, (ρ X : EReal) = ⨅ γ ∈ Γ, ⨅ X ∈ 𝒴, (γ X : EReal) := by
  apply le_antisymm
  · refine le_iInf fun γ => le_iInf fun hγ => le_iInf fun X => le_iInf fun hX => ?_
    apply iInf_le_of_le X
    apply iInf_le_of_le hX
    exact EReal.coe_le_coe ((h11 X).2 ⟨γ, hγ, rfl⟩)
  · refine le_iInf fun X => le_iInf fun hX => ?_
    obtain ⟨γ, hγ, he⟩ := (h11 X).1
    apply iInf_le_of_le γ
    apply iInf_le_of_le hγ
    apply iInf_le_of_le X
    apply iInf_le_of_le hX
    exact le_of_eq (congrArg (fun x : ℝ => (x : EReal)) he)

