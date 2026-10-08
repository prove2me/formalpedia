-- Prove2me | solution 1 for SuttonBartoRL.OffPolicy.tsitsiklis_van_roy_divergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:51:21.706978+00:00
-- url     : https://prove2.me/submissions/bd339918-f5ff-498e-8543-5e77200ca252

import Mathlib

open Filter in
theorem solution (ε γ : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∀ c u : ℝ,
      (∀ v : ℝ, (u - γ * (2 * c)) ^ 2 + (2 * u - (1 - ε) * γ * (2 * c)) ^ 2
          ≤ (v - γ * (2 * c)) ^ 2 + (2 * v - (1 - ε) * γ * (2 * c)) ^ 2)
        ↔ u = (6 - 4 * ε) / 5 * γ * c) ∧
    (∀ w : ℕ → ℝ,
      (∀ k (v : ℝ),
        (w (k + 1) - γ * (2 * w k)) ^ 2 + (2 * w (k + 1) - (1 - ε) * γ * (2 * w k)) ^ 2
          ≤ (v - γ * (2 * w k)) ^ 2 + (2 * v - (1 - ε) * γ * (2 * w k)) ^ 2) →
      5 / (6 - 4 * ε) < γ → w 0 ≠ 0 →
      Tendsto (fun k => |w k|) atTop atTop) := by
  have hdiff : ∀ c v : ℝ,
      (v - γ * (2 * c)) ^ 2 + (2 * v - (1 - ε) * γ * (2 * c)) ^ 2
        = ((6 - 4 * ε) / 5 * γ * c - γ * (2 * c)) ^ 2
          + (2 * ((6 - 4 * ε) / 5 * γ * c) - (1 - ε) * γ * (2 * c)) ^ 2
          + 5 * (v - (6 - 4 * ε) / 5 * γ * c) ^ 2 := by
    intro c v; ring
  have part1 : ∀ c u : ℝ,
      (∀ v : ℝ, (u - γ * (2 * c)) ^ 2 + (2 * u - (1 - ε) * γ * (2 * c)) ^ 2
          ≤ (v - γ * (2 * c)) ^ 2 + (2 * v - (1 - ε) * γ * (2 * c)) ^ 2)
        ↔ u = (6 - 4 * ε) / 5 * γ * c := by
    intro c u
    constructor
    · intro h
      have h1 := h ((6 - 4 * ε) / 5 * γ * c)
      have h2 := hdiff c u
      have h3 : (u - (6 - 4 * ε) / 5 * γ * c) ^ 2 = 0 :=
        le_antisymm (by nlinarith) (sq_nonneg _)
      have := (pow_eq_zero_iff two_ne_zero).mp h3
      linarith
    · rintro rfl v
      have h2 := hdiff c v
      nlinarith [sq_nonneg (v - (6 - 4 * ε) / 5 * γ * c)]
  refine ⟨part1, ?_⟩
  intro w hw hγ hw0
  set r : ℝ := (6 - 4 * ε) / 5 * γ with hr_def
  have hrec : ∀ k, w (k + 1) = r * w k := fun k => (part1 (w k) (w (k + 1))).mp (hw k)
  have hweq : ∀ k : ℕ, w k = r ^ k * w 0 := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [hrec, ih, pow_succ]; ring
  have hpos : 0 < 6 - 4 * ε := by linarith
  have h5 : 5 < γ * (6 - 4 * ε) := (div_lt_iff₀ hpos).mp hγ
  have hr : 1 < r := by
    have : r = γ * (6 - 4 * ε) / 5 := by rw [hr_def]; ring
    rw [this]; linarith
  have hr0 : 0 < r := by linarith
  have hw0' : 0 < |w 0| := abs_pos.mpr hw0
  have hfun : (fun k => |w k|) = fun k : ℕ => r ^ k * |w 0| := by
    funext k
    rw [hweq k, abs_mul, abs_pow, abs_of_pos hr0]
  rw [hfun]
  exact (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const hw0'
