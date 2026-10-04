-- Prove2me | solution 1 for TegmarkDimensionality.no_stable_orbits_above_three_dims
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:06:21.657957+00:00
-- url     : https://prove2.me/submissions/255df58f-1f3c-4f57-9dba-e90dc059662d

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace TegmarkAux

/-- Key estimate: with `q = (r₀/r)^2`, `U(r) - U(r₀) ≤ (q - 1) * C`. -/
theorem key_ineq (n : ℕ) (hn : 3 < n) (μ k L : ℝ) (hμ : 0 < μ) (hk : 0 < k)
    (r₀ r : ℝ) (hr₀ : 0 < r₀) (hr : 0 < r) :
    (L ^ 2 / (2 * μ * r ^ 2) - k * r ^ ((2 : ℝ) - n)) -
      (L ^ 2 / (2 * μ * r₀ ^ 2) - k * r₀ ^ ((2 : ℝ) - n)) ≤
      ((r₀ / r) ^ 2 - 1) *
        (L ^ 2 / (2 * μ * r₀ ^ 2) - k * r₀ ^ ((2 : ℝ) - n) * (((n : ℝ) - 2) / 2)) := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  set q : ℝ := (r₀ / r) ^ 2 with hq
  set p : ℝ := ((n : ℝ) - 2) / 2 with hp
  have hqpos : 0 < q := by positivity
  have hp1 : 1 ≤ p := by rw [hp]; linarith
  have hb : 0 < k * r₀ ^ ((2 : ℝ) - n) := mul_pos hk (Real.rpow_pos_of_pos hr₀ _)
  have hpow : r ^ ((2 : ℝ) - n) = r₀ ^ ((2 : ℝ) - n) * q ^ p := by
    rw [hq, ← Real.rpow_natCast (r₀ / r) 2, ← Real.rpow_mul (by positivity),
      Real.div_rpow hr₀.le hr.le]
    push_cast
    have h2 : (2 : ℝ) * p = -((2 : ℝ) - n) := by rw [hp]; ring
    rw [h2, Real.rpow_neg hr₀.le, Real.rpow_neg hr.le]
    have h3 : 0 < r₀ ^ ((2 : ℝ) - n) := Real.rpow_pos_of_pos hr₀ _
    field_simp
  have hL : L ^ 2 / (2 * μ * r ^ 2) = L ^ 2 / (2 * μ * r₀ ^ 2) * q := by
    rw [hq]; field_simp
  have hber : 1 + p * (q - 1) ≤ q ^ p := by
    have := one_add_mul_self_le_rpow_one_add (s := q - 1) (by linarith) hp1
    simpa using this
  rw [hpow, hL]
  nlinarith [hb, hber]

end TegmarkAux

open Filter Topology in
theorem solution (n : ℕ) (hn : 3 < n)
    (μ k L : ℝ) (hμ : 0 < μ) (hk : 0 < k) :
    ¬ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ᶠ r in 𝓝[≠] r₀,
        L ^ 2 / (2 * μ * r₀ ^ 2) - k * r₀ ^ ((2 : ℝ) - n) <
          L ^ 2 / (2 * μ * r ^ 2) - k * r ^ ((2 : ℝ) - n) := by
  rintro ⟨r₀, hr₀, h⟩
  set C : ℝ := L ^ 2 / (2 * μ * r₀ ^ 2) - k * r₀ ^ ((2 : ℝ) - n) * (((n : ℝ) - 2) / 2)
    with hC
  rcases le_or_gt C 0 with hc | hc
  · -- go left: r < r₀
    have h1 : ∀ᶠ r in 𝓝[<] r₀,
        L ^ 2 / (2 * μ * r₀ ^ 2) - k * r₀ ^ ((2 : ℝ) - n) <
          L ^ 2 / (2 * μ * r ^ 2) - k * r ^ ((2 : ℝ) - n) :=
      h.filter_mono (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Iio r₀) => ne_of_lt hx))
    have h2 : ∀ᶠ r in 𝓝[<] r₀, 0 < r :=
      nhdsWithin_le_nhds (lt_mem_nhds hr₀)
    have h3 : ∀ᶠ r in 𝓝[<] r₀, r < r₀ := self_mem_nhdsWithin
    obtain ⟨r, hP, hr, hrr⟩ := (h1.and (h2.and h3)).exists
    have hk' := TegmarkAux.key_ineq n hn μ k L hμ hk r₀ r hr₀ hr
    rw [← hC] at hk'
    have hq : 1 < (r₀ / r) ^ 2 := by
      have : 1 < r₀ / r := (one_lt_div hr).2 hrr
      nlinarith
    have : ((r₀ / r) ^ 2 - 1) * C ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
    linarith
  · -- go right: r > r₀
    have h1 : ∀ᶠ r in 𝓝[>] r₀,
        L ^ 2 / (2 * μ * r₀ ^ 2) - k * r₀ ^ ((2 : ℝ) - n) <
          L ^ 2 / (2 * μ * r ^ 2) - k * r ^ ((2 : ℝ) - n) :=
      h.filter_mono (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Ioi r₀) => ne_of_gt hx))
    have h3 : ∀ᶠ r in 𝓝[>] r₀, r₀ < r := self_mem_nhdsWithin
    obtain ⟨r, hP, hrr⟩ := (h1.and h3).exists
    have hr : 0 < r := lt_trans hr₀ hrr
    have hk' := TegmarkAux.key_ineq n hn μ k L hμ hk r₀ r hr₀ hr
    rw [← hC] at hk'
    have hq : (r₀ / r) ^ 2 < 1 := by
      have h0 : 0 < r₀ / r := by positivity
      have : r₀ / r < 1 := (div_lt_one hr).2 hrr
      nlinarith
    have : ((r₀ / r) ^ 2 - 1) * C < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hc
    linarith
