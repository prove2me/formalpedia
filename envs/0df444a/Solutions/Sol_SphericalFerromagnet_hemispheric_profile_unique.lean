-- Prove2me | solution 1 for SphericalFerromagnet.hemispheric_profile_unique
-- status  : ACCEPTED   (disprove)
-- author  : @shivm
-- created : 2026-10-05T06:24:04.036997+00:00
-- url     : https://prove2.me/submissions/2a239dd9-0dfd-4756-84e2-7240cb9cb479

import Definitions.Def_spherical_ferromagnet_profile_defs
import Definitions.Def_sf241_second_profile

open scoped ContDiff
open SphericalFerromagnet

/-- Uniqueness fails at `κ = 4`: `2θ` and the reflected shot are two different
`H_{0,2}` critical profiles. -/
theorem solution :
    ¬ (∀ (κ : ℝ) (hκ : 4 ≤ κ),
      ∃ h : ℝ → ℝ, IsH02CriticalProfile κ h ∧
        ∀ g : ℝ → ℝ, IsH02CriticalProfile κ g → ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, g θ = h θ) := by
  intro H
  obtain ⟨h, -, huniq⟩ := H 4 le_rfl
  obtain ⟨g, hg, θ, hθ, hne⟩ := SF241.exists_second_profile_kappa_four'
  exact hne ((huniq g hg θ hθ).trans (huniq _ SF241.two_theta_isH02CriticalProfile' θ hθ).symm)
