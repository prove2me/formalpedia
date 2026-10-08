-- Prove2me | solution 1 for RWPI.SqrtLasso.eq_29_minimization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:15:27.071279+00:00
-- url     : https://prove2.me/submissions/9acd133a-c591-4136-a10c-978a832c4c3f

import Mathlib

namespace F6f29a23Aux

lemma key (m b s γ : ℝ) (h : b ^ 2 < γ) :
    γ * s ^ 2 + γ / (γ - b ^ 2) * m ^ 2
      = (m + b * s) ^ 2 + ((γ - b ^ 2) * s - b * m) ^ 2 / (γ - b ^ 2) := by
  have hu : γ - b ^ 2 ≠ 0 := by linarith
  field_simp
  ring

lemma key2 (M b δ γ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (h : b ^ 2 < γ) :
    γ * δ + γ / (γ - b ^ 2) * M
      = (Real.sqrt M + b * Real.sqrt δ) ^ 2
        + ((γ - b ^ 2) * Real.sqrt δ - b * Real.sqrt M) ^ 2 / (γ - b ^ 2) := by
  have := key (Real.sqrt M) b (Real.sqrt δ) γ h
  rwa [Real.sq_sqrt hδ, Real.sq_sqrt hM] at this

end F6f29a23Aux

theorem solution (M b δ : ℝ) (hM : 0 ≤ M) (hb : 0 ≤ b) (hδ : 0 ≤ δ) :
    IsGLB {v : ℝ | ∃ γ : ℝ, b ^ 2 < γ ∧ v = γ * δ + γ / (γ - b ^ 2) * M}
      ((Real.sqrt M + b * Real.sqrt δ) ^ 2) := by
  constructor
  · rintro v ⟨γ, hγ, rfl⟩
    rw [F6f29a23Aux.key2 M b δ γ hM hδ hγ]
    have : 0 < γ - b ^ 2 := by linarith
    have : 0 ≤ ((γ - b ^ 2) * Real.sqrt δ - b * Real.sqrt M) ^ 2 / (γ - b ^ 2) := by positivity
    linarith
  · intro y hy
    by_contra hlt
    rw [not_le] at hlt
    set x := (Real.sqrt M + b * Real.sqrt δ) ^ 2 with hx
    set ε := y - x with hε
    have hεpos : 0 < ε := by linarith
    set m := Real.sqrt M
    set s := Real.sqrt δ
    have hm0 : 0 ≤ m := Real.sqrt_nonneg _
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    -- find u > 0 with (u*s - b*m)^2/u < ε
    have hex : ∃ u : ℝ, 0 < u ∧ (u * s - b * m) ^ 2 / u < ε := by
      rcases eq_or_lt_of_le hs0 with hs | hs
      · rw [← hs]
        refine ⟨(b * m) ^ 2 / ε + 1, by positivity, ?_⟩
        have hpos : 0 < (b * m) ^ 2 / ε + 1 := by positivity
        rw [div_lt_iff₀ hpos]
        have : ε * ((b * m) ^ 2 / ε + 1) = (b * m) ^ 2 + ε := by
          field_simp
        nlinarith
      · set η := ε / (2 * s ^ 2) with hη
        have hηpos : 0 < η := by positivity
        have hbm : 0 ≤ b * m / s := by positivity
        refine ⟨b * m / s + η, by linarith, ?_⟩
        have hpos : 0 < b * m / s + η := by linarith
        have e1 : (b * m / s + η) * s - b * m = η * s := by
          field_simp
          ring
        rw [e1, div_lt_iff₀ hpos]
        have e2 : η * s ^ 2 = ε / 2 := by
          rw [hη]; field_simp
        nlinarith [mul_nonneg hbm hεpos.le]
    obtain ⟨u, hu, hlt2⟩ := hex
    have hmem : (b ^ 2 + u) * δ + (b ^ 2 + u) / (b ^ 2 + u - b ^ 2) * M ∈
        {v : ℝ | ∃ γ : ℝ, b ^ 2 < γ ∧ v = γ * δ + γ / (γ - b ^ 2) * M} :=
      ⟨b ^ 2 + u, by linarith, rfl⟩
    have h1 := hy hmem
    rw [F6f29a23Aux.key2 M b δ (b ^ 2 + u) hM hδ (by linarith)] at h1
    have h2 : b ^ 2 + u - b ^ 2 = u := by ring
    rw [h2] at h1
    linarith
