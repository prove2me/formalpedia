-- Prove2me | solution 1 for StarShapedRisk.LawInvariant.eq7_rho_isLeast_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:36.872958+00:00
-- url     : https://prove2.me/submissions/63b55b15-79c5-439a-8807-d4e402ae1147

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_Model
set_option autoImplicit false
open StarShapedRisk.LawInvariant

/-- Castagnoli et al. (2022), Eq. (7) (p. 2642), on the space of bounded measurable positions:
a risk measure is recovered from its acceptance set as an attained minimum,
`ρ X = min {m ∈ ℝ | X - m ∈ A_ρ}`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Positions Ω → ℝ) (hρ : IsRiskMeasure ρ) (X : Positions Ω) :
    IsLeast {m : ℝ | X - const m ∈ acceptanceSetOf ρ} (ρ X) := by
  have he (m : ℝ) : X - const m ∈ acceptanceSetOf ρ ↔ ρ X ≤ m := by
    change ρ (X - const m) ≤ 0 ↔ _
    rw [hρ.2.1 X m]
    exact sub_nonpos
  exact ⟨(he (ρ X)).mpr le_rfl, fun m hm => (he m).mp hm⟩


