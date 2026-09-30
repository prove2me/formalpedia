-- Prove2me | solution 1 for StarShapedRisk.Representation.eq7_min_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:37.616145+00:00
-- url     : https://prove2.me/submissions/c514bdbc-f6d7-4dcd-90dd-4289c98caf41

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_AcceptanceSet
set_option autoImplicit false
open StarShapedRisk.Representation
theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsRiskMeasure 𝒳 ρ) (X : 𝒳.carrier) :
    IsLeast {m : ℝ | X - 𝒳.const m ∈ acceptanceSet 𝒳 ρ} (ρ X) := by
  have he (m : ℝ) : X - 𝒳.const m ∈ acceptanceSet 𝒳 ρ ↔ ρ X ≤ m := by
    change ρ (X - 𝒳.const m) ≤ 0 ↔ _
    rw [hρ.2.1 X m]
    exact sub_nonpos
  exact ⟨(he (ρ X)).mpr le_rfl, fun m hm => (he m).mp hm⟩

