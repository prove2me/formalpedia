-- Prove2me | solution 1 for WeierstrassCurve.eq_zero_of_firstOrderVariableChange_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a9508190-cffc-5ab8-83c1-f02a0f323309

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero

set_option autoImplicit false

theorem solution
    (R : Type) [CommRing R] (E : WeierstrassCurve R) [E.IsElliptic] (μ ρ ς τ : R)
    (h₁ : E.a₁ * μ + 2 * ς = 0)
    (h₂ : 2 * E.a₂ * μ + 3 * ρ - E.a₁ * ς = 0)
    (h₃ : 3 * E.a₃ * μ + E.a₁ * ρ + 2 * τ = 0)
    (h₄ : 4 * E.a₄ * μ + 2 * E.a₂ * ρ - E.a₃ * ς - E.a₁ * τ = 0)
    (h₆ : 6 * E.a₆ * μ + E.a₄ * ρ - E.a₃ * τ = 0) :
    μ = 0 ∧ ρ = 0 ∧ ς = 0 ∧ τ = 0 := by
  have hΔ : IsUnit E.Δ := WeierstrassCurve.isUnit_Δ E
  have eμ : E.Δ * μ = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (-E.a₁^5 * E.a₆ + E.a₁^4 * E.a₃ * E.a₄ - E.a₁^3 * E.a₂ * E.a₃^2 - 8 * E.a₁^3 * E.a₂ * E.a₆ + E.a₁^3 * E.a₄^2 + 4 * E.a₁^2 * E.a₂ * E.a₃ * E.a₄ + E.a₁^2 * E.a₃^3 + 12 * E.a₁^2 * E.a₃ * E.a₆ - 4 * E.a₁ * E.a₂^2 * E.a₃^2 - 16 * E.a₁ * E.a₂^2 * E.a₆ + 4 * E.a₁ * E.a₂ * E.a₄^2 - 5 * E.a₁ * E.a₃^2 * E.a₄ + 12 * E.a₁ * E.a₄ * E.a₆ + 6 * E.a₂ * E.a₃^3 + 24 * E.a₂ * E.a₃ * E.a₆ - 8 * E.a₃ * E.a₄^2) * h₁
      + (-2 * E.a₁^4 * E.a₆ + 2 * E.a₁^3 * E.a₃ * E.a₄ - 2 * E.a₁^2 * E.a₂ * E.a₃^2 - 16 * E.a₁^2 * E.a₂ * E.a₆ + 2 * E.a₁^2 * E.a₄^2 + 8 * E.a₁ * E.a₂ * E.a₃ * E.a₄ + 3 * E.a₁ * E.a₃^3 + 12 * E.a₁ * E.a₃ * E.a₆ - 8 * E.a₂^2 * E.a₃^2 - 32 * E.a₂^2 * E.a₆ + 8 * E.a₂ * E.a₄^2 + 6 * E.a₃^2 * E.a₄ + 24 * E.a₄ * E.a₆) * h₂
      + (6 * E.a₁^3 * E.a₆ - 7 * E.a₁^2 * E.a₃ * E.a₄ + 8 * E.a₁ * E.a₂ * E.a₃^2 + 24 * E.a₁ * E.a₂ * E.a₆ - 8 * E.a₁ * E.a₄^2 + 4 * E.a₂ * E.a₃ * E.a₄ - 9 * E.a₃^3 - 36 * E.a₃ * E.a₆) * h₃
      + (-E.a₁^2 * E.a₃^2 + 12 * E.a₁^2 * E.a₆ - 16 * E.a₁ * E.a₃ * E.a₄ + 12 * E.a₂ * E.a₃^2 + 48 * E.a₂ * E.a₆ - 16 * E.a₄^2) * h₄
      + (E.a₁^3 * E.a₃ + 2 * E.a₁^2 * E.a₄ + 4 * E.a₁ * E.a₂ * E.a₃ + 8 * E.a₂ * E.a₄ - 18 * E.a₃^2 - 72 * E.a₆) * h₆
  have eρ : E.Δ * ρ = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (3 * E.a₁^4 * E.a₃ * E.a₆ - 3 * E.a₁^3 * E.a₃^2 * E.a₄ + 8 * E.a₁^3 * E.a₄ * E.a₆ + 3 * E.a₁^2 * E.a₂ * E.a₃^3 + 8 * E.a₁^2 * E.a₂ * E.a₃ * E.a₆ - 11 * E.a₁^2 * E.a₃ * E.a₄^2 + 12 * E.a₁ * E.a₂ * E.a₃^2 * E.a₄ + 32 * E.a₁ * E.a₂ * E.a₄ * E.a₆ - 3 * E.a₁ * E.a₃^4 - 30 * E.a₁ * E.a₃^2 * E.a₆ - 8 * E.a₁ * E.a₄^3 - 72 * E.a₁ * E.a₆^2 - 4 * E.a₂^2 * E.a₃^3 - 16 * E.a₂^2 * E.a₃ * E.a₆ + 4 * E.a₂ * E.a₃ * E.a₄^2 + 3 * E.a₃^3 * E.a₄ + 12 * E.a₃ * E.a₄ * E.a₆) * h₁
      + (8 * E.a₁^3 * E.a₃ * E.a₆ - 8 * E.a₁^2 * E.a₃^2 * E.a₄ + 16 * E.a₁^2 * E.a₄ * E.a₆ + 8 * E.a₁ * E.a₂ * E.a₃^3 + 32 * E.a₁ * E.a₂ * E.a₃ * E.a₆ - 24 * E.a₁ * E.a₃ * E.a₄^2 + 16 * E.a₂ * E.a₃^2 * E.a₄ + 64 * E.a₂ * E.a₄ * E.a₆ - 9 * E.a₃^4 - 72 * E.a₃^2 * E.a₆ - 16 * E.a₄^3 - 144 * E.a₆^2) * h₂
      + (-E.a₁^5 * E.a₆ + E.a₁^4 * E.a₃ * E.a₄ - E.a₁^3 * E.a₂ * E.a₃^2 - 8 * E.a₁^3 * E.a₂ * E.a₆ + E.a₁^3 * E.a₄^2 + 4 * E.a₁^2 * E.a₂ * E.a₃ * E.a₄ + E.a₁^2 * E.a₃^3 + 12 * E.a₁^2 * E.a₃ * E.a₆ - 4 * E.a₁ * E.a₂^2 * E.a₃^2 - 16 * E.a₁ * E.a₂^2 * E.a₆ + 4 * E.a₁ * E.a₂ * E.a₄^2 - 5 * E.a₁ * E.a₃^2 * E.a₄ + 12 * E.a₁ * E.a₄ * E.a₆ + 6 * E.a₂ * E.a₃^3 + 24 * E.a₂ * E.a₃ * E.a₆ - 8 * E.a₃ * E.a₄^2) * h₃
      + (-2 * E.a₁^4 * E.a₆ + 2 * E.a₁^3 * E.a₃ * E.a₄ - 2 * E.a₁^2 * E.a₂ * E.a₃^2 - 16 * E.a₁^2 * E.a₂ * E.a₆ + 2 * E.a₁^2 * E.a₄^2 + 8 * E.a₁ * E.a₂ * E.a₃ * E.a₄ + 3 * E.a₁ * E.a₃^3 + 12 * E.a₁ * E.a₃ * E.a₆ - 8 * E.a₂^2 * E.a₃^2 - 32 * E.a₂^2 * E.a₆ + 8 * E.a₂ * E.a₄^2 + 6 * E.a₃^2 * E.a₄ + 24 * E.a₄ * E.a₆) * h₄
      + (-E.a₁^2 * E.a₃^2 + 12 * E.a₁^2 * E.a₆ - 16 * E.a₁ * E.a₃ * E.a₄ + 12 * E.a₂ * E.a₃^2 + 48 * E.a₂ * E.a₆ - 16 * E.a₄^2) * h₆
  have eς : E.Δ * ς = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (-2 * E.a₁^4 * E.a₂ * E.a₆ + 2 * E.a₁^3 * E.a₂ * E.a₃ * E.a₄ + 9 * E.a₁^3 * E.a₃ * E.a₆ - 2 * E.a₁^2 * E.a₂^2 * E.a₃^2 - 16 * E.a₁^2 * E.a₂^2 * E.a₆ + 2 * E.a₁^2 * E.a₂ * E.a₄^2 - 9 * E.a₁^2 * E.a₃^2 * E.a₄ + 30 * E.a₁^2 * E.a₄ * E.a₆ + 8 * E.a₁ * E.a₂^2 * E.a₃ * E.a₄ + 11 * E.a₁ * E.a₂ * E.a₃^3 + 48 * E.a₁ * E.a₂ * E.a₃ * E.a₆ - 40 * E.a₁ * E.a₃ * E.a₄^2 - 8 * E.a₂^3 * E.a₃^2 - 32 * E.a₂^3 * E.a₆ + 8 * E.a₂^2 * E.a₄^2 + 34 * E.a₂ * E.a₃^2 * E.a₄ + 144 * E.a₂ * E.a₄ * E.a₆ - 9 * E.a₃^4 - 90 * E.a₃^2 * E.a₆ - 32 * E.a₄^3 - 216 * E.a₆^2) * h₁
      + (E.a₁^5 * E.a₆ - E.a₁^4 * E.a₃ * E.a₄ + E.a₁^3 * E.a₂ * E.a₃^2 + 8 * E.a₁^3 * E.a₂ * E.a₆ - E.a₁^3 * E.a₄^2 - 4 * E.a₁^2 * E.a₂ * E.a₃ * E.a₄ - E.a₁^2 * E.a₃^3 - 12 * E.a₁^2 * E.a₃ * E.a₆ + 4 * E.a₁ * E.a₂^2 * E.a₃^2 + 16 * E.a₁ * E.a₂^2 * E.a₆ - 4 * E.a₁ * E.a₂ * E.a₄^2 + 5 * E.a₁ * E.a₃^2 * E.a₄ - 12 * E.a₁ * E.a₄ * E.a₆ - 6 * E.a₂ * E.a₃^3 - 24 * E.a₂ * E.a₃ * E.a₆ + 8 * E.a₃ * E.a₄^2) * h₂
      + (-3 * E.a₁^4 * E.a₆ + 3 * E.a₁^3 * E.a₃ * E.a₄ - 3 * E.a₁^2 * E.a₂ * E.a₃^2 - 12 * E.a₁^2 * E.a₂ * E.a₆ + 4 * E.a₁^2 * E.a₄^2 - 4 * E.a₁ * E.a₂ * E.a₃ * E.a₄ + 3 * E.a₁ * E.a₃^3 + 36 * E.a₁ * E.a₃ * E.a₆ + 4 * E.a₂^2 * E.a₃^2 - 12 * E.a₃^2 * E.a₄) * h₃
      + (-6 * E.a₁^3 * E.a₆ + 7 * E.a₁^2 * E.a₃ * E.a₄ - 8 * E.a₁ * E.a₂ * E.a₃^2 - 24 * E.a₁ * E.a₂ * E.a₆ + 8 * E.a₁ * E.a₄^2 - 4 * E.a₂ * E.a₃ * E.a₄ + 9 * E.a₃^3 + 36 * E.a₃ * E.a₆) * h₄
      + (-E.a₁^3 * E.a₄ + 2 * E.a₁^2 * E.a₂ * E.a₃ - 4 * E.a₁ * E.a₂ * E.a₄ - 3 * E.a₁ * E.a₃^2 + 36 * E.a₁ * E.a₆ + 8 * E.a₂^2 * E.a₃ - 24 * E.a₃ * E.a₄) * h₆
  have eτ : E.Δ * τ = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (-4 * E.a₁^4 * E.a₄ * E.a₆ + 8 * E.a₁^3 * E.a₂ * E.a₃ * E.a₆ + 4 * E.a₁^3 * E.a₃ * E.a₄^2 - 12 * E.a₁^2 * E.a₂ * E.a₃^2 * E.a₄ - 16 * E.a₁^2 * E.a₂ * E.a₄ * E.a₆ - 3 * E.a₁^2 * E.a₃^2 * E.a₆ + 4 * E.a₁^2 * E.a₄^3 + 36 * E.a₁^2 * E.a₆^2 + 8 * E.a₁ * E.a₂^2 * E.a₃^3 + 32 * E.a₁ * E.a₂^2 * E.a₃ * E.a₆ - 8 * E.a₁ * E.a₂ * E.a₃ * E.a₄^2 + 6 * E.a₁ * E.a₃^3 * E.a₄ - 24 * E.a₁ * E.a₃ * E.a₄ * E.a₆ - 9 * E.a₂ * E.a₃^4 - 36 * E.a₂ * E.a₃^2 * E.a₆ + 12 * E.a₃^2 * E.a₄^2) * h₁
      + (-E.a₁^4 * E.a₃ * E.a₆ + E.a₁^3 * E.a₃^2 * E.a₄ - 8 * E.a₁^3 * E.a₄ * E.a₆ - E.a₁^2 * E.a₂ * E.a₃^3 + 8 * E.a₁^2 * E.a₂ * E.a₃ * E.a₆ + 9 * E.a₁^2 * E.a₃ * E.a₄^2 - 20 * E.a₁ * E.a₂ * E.a₃^2 * E.a₄ - 32 * E.a₁ * E.a₂ * E.a₄ * E.a₆ + 18 * E.a₁ * E.a₃^2 * E.a₆ + 8 * E.a₁ * E.a₄^3 + 72 * E.a₁ * E.a₆^2 + 12 * E.a₂^2 * E.a₃^3 + 48 * E.a₂^2 * E.a₃ * E.a₆ - 12 * E.a₂ * E.a₃ * E.a₄^2 - 9 * E.a₃^3 * E.a₄ - 36 * E.a₃ * E.a₄ * E.a₆) * h₂
      + (-2 * E.a₁^4 * E.a₂ * E.a₆ + 2 * E.a₁^3 * E.a₂ * E.a₃ * E.a₄ + 3 * E.a₁^3 * E.a₃ * E.a₆ - 2 * E.a₁^2 * E.a₂^2 * E.a₃^2 - 16 * E.a₁^2 * E.a₂^2 * E.a₆ + 2 * E.a₁^2 * E.a₂ * E.a₄^2 - 2 * E.a₁^2 * E.a₃^2 * E.a₄ + 30 * E.a₁^2 * E.a₄ * E.a₆ + 8 * E.a₁ * E.a₂^2 * E.a₃ * E.a₄ + 3 * E.a₁ * E.a₂ * E.a₃^3 + 24 * E.a₁ * E.a₂ * E.a₃ * E.a₆ - 32 * E.a₁ * E.a₃ * E.a₄^2 - 8 * E.a₂^3 * E.a₃^2 - 32 * E.a₂^3 * E.a₆ + 8 * E.a₂^2 * E.a₄^2 + 30 * E.a₂ * E.a₃^2 * E.a₄ + 144 * E.a₂ * E.a₄ * E.a₆ - 54 * E.a₃^2 * E.a₆ - 32 * E.a₄^3 - 216 * E.a₆^2) * h₃
      + (E.a₁^5 * E.a₆ - E.a₁^4 * E.a₃ * E.a₄ + E.a₁^3 * E.a₂ * E.a₃^2 + 8 * E.a₁^3 * E.a₂ * E.a₆ - E.a₁^3 * E.a₄^2 - 4 * E.a₁^2 * E.a₂ * E.a₃ * E.a₄ - 24 * E.a₁^2 * E.a₃ * E.a₆ + 4 * E.a₁ * E.a₂^2 * E.a₃^2 + 16 * E.a₁ * E.a₂^2 * E.a₆ - 4 * E.a₁ * E.a₂ * E.a₄^2 + 21 * E.a₁ * E.a₃^2 * E.a₄ - 12 * E.a₁ * E.a₄ * E.a₆ - 18 * E.a₂ * E.a₃^3 - 72 * E.a₂ * E.a₃ * E.a₆ + 24 * E.a₃ * E.a₄^2) * h₄
      + (-E.a₁^3 * E.a₃^2 - 6 * E.a₁^3 * E.a₆ + 5 * E.a₁^2 * E.a₃ * E.a₄ - 12 * E.a₁ * E.a₂ * E.a₃^2 - 24 * E.a₁ * E.a₂ * E.a₆ + 8 * E.a₁ * E.a₄^2 - 12 * E.a₂ * E.a₃ * E.a₄ + 27 * E.a₃^3 + 108 * E.a₃ * E.a₆) * h₆
  exact ⟨hΔ.mul_right_eq_zero.mp eμ, hΔ.mul_right_eq_zero.mp eρ, hΔ.mul_right_eq_zero.mp eς, hΔ.mul_right_eq_zero.mp eτ⟩

end S_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero (solution)
