-- Prove2me | solution 1 for TTSABilevel.SC.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:05:53.31867+00:00
-- url     : https://prove2.me/submissions/934017da-12f4-4cb8-b47d-4e13e7c7f728

import Mathlib
set_option autoImplicit false

theorem solution (q a : ℝ) (γ : ℕ → ℝ)
    (hq1 : 1 < q) (hq2 : q ≤ 2) (ha : 0 < a)
    (hmono : Antitone γ) (hnonneg : ∀ j, 0 ≤ γ j)
    (hfirst : γ 0 < 1 / (2 * a))
    (hratio : ∀ ℓ, 1 ≤ ℓ → γ (ℓ - 1) ≤ (1 + a / (2 * (q - 1)) * γ ℓ) * γ ℓ) :
    ∀ k : ℕ,
      (∑ j ∈ Finset.range (k + 1),
        (γ j) ^ q * ∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) ≤
        2 / a * (γ k) ^ (q - 1) := by
  have hq0 : 0 < q - 1 := by linarith
  have hsmall : ∀ k, γ k * a ≤ 1 / 2 := by
    intro k
    have h1 : γ k ≤ γ 0 := hmono (Nat.zero_le k)
    have h2 : γ 0 * (2 * a) < 1 := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * a)).mp hfirst
      exact this
    nlinarith [hnonneg k]
  -- the pow identity
  have hpow : ∀ x : ℝ, 0 ≤ x → x ^ q = x ^ (q - 1) * x := by
    intro x hx
    have h := Real.rpow_add' hx (show q - 1 + 1 ≠ 0 by linarith)
    rw [show q - 1 + 1 = q by ring, Real.rpow_one] at h
    exact h
  -- recurrence
  have hrec : ∀ k : ℕ,
      (∑ j ∈ Finset.range (k + 1 + 1),
        (γ j) ^ q * ∏ ℓ ∈ Finset.Icc (j + 1) (k + 1), (1 - γ ℓ * a)) =
      (γ (k + 1)) ^ q + (1 - γ (k + 1) * a) *
      (∑ j ∈ Finset.range (k + 1),
        (γ j) ^ q * ∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) := by
    intro k
    rw [Finset.sum_range_succ]
    have hE : Finset.Icc (k + 1 + 1) (k + 1) = ∅ := by
      ext x; simp
    rw [hE, Finset.prod_empty, mul_one, Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 ≤ k + 1 := by
      have := Finset.mem_range.mp hj; omega
    rw [Finset.prod_Icc_succ_top hj']
    ring
  intro k
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    have hE : Finset.Icc (0 + 1) 0 = ∅ := by
      ext x; simp
    rw [hE, Finset.prod_empty, mul_one, hpow _ (hnonneg 0)]
    have hG : 0 ≤ γ 0 ^ (q - 1) := Real.rpow_nonneg (hnonneg 0) _
    have : γ 0 * a ≤ 1 / 2 := hsmall 0
    have h2 : γ 0 ≤ 2 / a := by
      rw [le_div_iff₀ ha]; linarith
    nlinarith
  | succ k ih =>
    rw [hrec k]
    set x := γ (k + 1) with hx
    have hx0 : 0 ≤ x := hnonneg _
    have hxa : x * a ≤ 1 / 2 := hsmall _
    have hy0 : 0 ≤ γ k := hnonneg _
    have hr := hratio (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hr
    set c := a / (2 * (q - 1)) * x with hc
    have hc0 : 0 ≤ c := by positivity
    have hG0 : 0 ≤ x ^ (q - 1) := Real.rpow_nonneg hx0 _
    have hb : (1 + c) ^ (q - 1) ≤ 1 + (q - 1) * c :=
      rpow_one_add_le_one_add_mul_self (by linarith) hq0.le (by linarith)
    have hyk : γ k ^ (q - 1) ≤ (1 + a * x / 2) * x ^ (q - 1) := by
      calc γ k ^ (q - 1) ≤ ((1 + c) * x) ^ (q - 1) :=
            Real.rpow_le_rpow hy0 hr hq0.le
        _ = (1 + c) ^ (q - 1) * x ^ (q - 1) :=
            Real.mul_rpow (by linarith) hx0
        _ ≤ (1 + (q - 1) * c) * x ^ (q - 1) :=
            mul_le_mul_of_nonneg_right hb hG0
        _ = (1 + a * x / 2) * x ^ (q - 1) := by
            congr 1
            rw [hc]; field_simp
    have h1 : 0 ≤ 1 - x * a := by linarith
    rw [hpow x hx0]
    have h2 : (1 - x * a) * (2 / a * γ k ^ (q - 1)) ≤
        (1 - x * a) * (2 / a * ((1 + a * x / 2) * x ^ (q - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyk (by positivity)) h1
    have h3 : x ^ (q - 1) * x + (1 - x * a) * (2 / a * ((1 + a * x / 2) * x ^ (q - 1)))
        ≤ 2 / a * x ^ (q - 1) := by
      have e : x ^ (q - 1) * x + (1 - x * a) * (2 / a * ((1 + a * x / 2) * x ^ (q - 1)))
          = 2 / a * x ^ (q - 1) - x * x * a * x ^ (q - 1) := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ x * x * a * x ^ (q - 1) := by positivity
      linarith
    have h4 : (1 - x * a) * (∑ j ∈ Finset.range (k + 1),
        (γ j) ^ q * ∏ ℓ ∈ Finset.Icc (j + 1) k, (1 - γ ℓ * a)) ≤
        (1 - x * a) * (2 / a * γ k ^ (q - 1)) :=
      mul_le_mul_of_nonneg_left ih h1
    linarith
