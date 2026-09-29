-- Prove2me | solution 1 for SphericalGeometry.greatCirclePath_shift_rational_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T05:49:17.229093+00:00
-- url     : https://prove2.me/submissions/b1c754f6-f622-4d9a-ab41-6083930a0b4d

import Definitions.Def_spherical_great_circle
import Theorems.Thm_SphericalGeometry_greatCirclePath_period

open SphericalGeometry

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Subgroup (E ≃ₗᵢ[ℝ] E)) [Fintype G]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0)
    (w : G) (c : ℝ)
    (hc : ∀ s : ℝ, greatCirclePath v1 v2 (s + c)
      = (w : E ≃ₗᵢ[ℝ] E) (greatCirclePath v1 v2 s)) :
    ∃ k : ℕ, 0 < k ∧ k ∣ Fintype.card G ∧
      ∃ n : ℤ, (k : ℝ) * c = (n : ℝ) * (2 * Real.pi) := by
  refine ⟨orderOf w, orderOf_pos w, orderOf_dvd_card, ?_⟩
  have key : ∀ (j : ℕ) (s : ℝ), greatCirclePath v1 v2 (s + (j : ℝ) * c)
      = ((w : E ≃ₗᵢ[ℝ] E) ^ j) (greatCirclePath v1 v2 s) := by
    intro j
    induction j with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      have hstep : s + ((n : ℝ) + 1) * c = (s + (n : ℝ) * c) + c := by ring
      have hstep' := hc (s + (n : ℝ) * c)
      push_cast
      rw [hstep, hstep', ih s, pow_succ']
      rfl
  have hone : ((w : E ≃ₗᵢ[ℝ] E) ^ (orderOf w)) = 1 := by
    have hpow : (w ^ (orderOf w) : G) = 1 := pow_orderOf_eq_one w
    have hcoe : ((w ^ (orderOf w) : G) : E ≃ₗᵢ[ℝ] E)
        = (w : E ≃ₗᵢ[ℝ] E) ^ (orderOf w) := by push_cast; rfl
    rw [← hcoe, hpow]
    rfl
  have hT : greatCirclePath v1 v2 ((orderOf w : ℝ) * c) = greatCirclePath v1 v2 0 := by
    have hk := key (orderOf w) 0
    rw [zero_add] at hk
    rw [hk, hone]
    rfl
  exact greatCirclePath_period v1 v2 h1 h2 ho _ hT
