-- Prove2me | solution 1 for WeightedCongestionBR.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:18:00.235791+00:00
-- url     : https://prove2.me/submissions/c3013616-1b6d-4eef-aee6-9a81de19b0f2

import Mathlib
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_WeightedCongestionBR_smoothSet
set_option autoImplicit false
open scoped NNReal

namespace Aux_WCBR_l2

open WeightedCongestionBR

/-- Weighted AM-GM: `(N+1) u v^N ≤ u^(N+1) + N v^(N+1)`. -/
theorem amgm (N : ℕ) (hN : 1 ≤ N) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((N : ℝ) + 1) * u * v ^ N ≤ u ^ (N + 1) + (N : ℝ) * v ^ (N + 1) := by
  rcases hv.lt_or_eq with hv | hv
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = u / v := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hu hv.le
    have hu' : u = t * v := by rw [ht, div_mul_cancel₀ u hv.ne']
    subst hu'
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ t - 1 by linarith) (N + 1)
    rw [show (1 : ℝ) + (t - 1) = t by ring] at hb
    push_cast at hb
    have key := mul_le_mul_of_nonneg_right hb (pow_nonneg hv.le (N + 1))
    rw [mul_pow, pow_succ v N]
    rw [pow_succ v N] at key
    linarith [key]
  · subst hv
    rw [zero_pow (show N ≠ 0 by omega), zero_pow (show N + 1 ≠ 0 by omega)]
    simp only [mul_zero, add_zero]
    exact pow_nonneg hu _

/-- Convexity: `Φ^N (x+y)^(N+1) ≤ Φ^N P^N y^(N+1) + P^N x^(N+1)` with `P = Φ + 1`. -/
theorem conv (N : ℕ) (Φ : ℝ) (hΦ : 0 < Φ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Φ ^ N * (x + y) ^ (N + 1) ≤ Φ ^ N * (Φ + 1) ^ N * y ^ (N + 1) + (Φ + 1) ^ N * x ^ (N + 1) := by
  have hP : 0 < Φ + 1 := by linarith
  have hΦne : Φ ≠ 0 := hΦ.ne'
  have hPne : Φ + 1 ≠ 0 := hP.ne'
  have hconv := (convexOn_pow (𝕜 := ℝ) (N + 1)).2
    (Set.mem_Ici.mpr (mul_nonneg hP.le hy))
    (Set.mem_Ici.mpr (div_nonneg (mul_nonneg hP.le hx) hΦ.le))
    (div_nonneg zero_le_one hP.le) (div_nonneg hΦ.le hP.le)
    (show 1 / (Φ + 1) + Φ / (Φ + 1) = 1 by field_simp; try ring)
  simp only [smul_eq_mul] at hconv
  have e1 : 1 / (Φ + 1) * ((Φ + 1) * y) + Φ / (Φ + 1) * ((Φ + 1) * x / Φ) = x + y := by
    field_simp
    try ring
  rw [e1] at hconv
  have e2 : Φ ^ N * (1 / (Φ + 1) * ((Φ + 1) * y) ^ (N + 1) +
      Φ / (Φ + 1) * ((Φ + 1) * x / Φ) ^ (N + 1)) =
      Φ ^ N * (Φ + 1) ^ N * y ^ (N + 1) + (Φ + 1) ^ N * x ^ (N + 1) := by
    have hΦ' : Φ ≠ 0 := hΦ.ne'
    have hP' : Φ + 1 ≠ 0 := hP.ne'
    rw [mul_pow, div_pow, mul_pow]
    field_simp
    try ring
  rw [← e2]
  exact mul_le_mul_of_nonneg_left hconv (pow_nonneg hΦ.le N)

/-- The degree-`(n+1)` two-variable inequality with the tangent coefficients. -/
theorem degD (n : ℕ) (Φ : ℝ) (hΦ : 0 < Φ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y * (x + y) ^ (n + 1) ≤
      (Φ + 1) ^ n * ((Φ + 1) + ((n : ℝ) + 1)) / ((n : ℝ) + 2) * (y * y ^ (n + 1)) +
      ((n : ℝ) + 1) * (Φ + 1) ^ n / (((n : ℝ) + 2) * Φ ^ (n + 1)) * (x * x ^ (n + 1)) := by
  have hP : 0 < Φ + 1 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have A := amgm (n + 1) (by omega) ((Φ + 1) * y) (x + y) (mul_nonneg hP.le hy) (by linarith)
  push_cast at A
  have Cv := conv (n + 1) Φ hΦ x y hx hy
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((n : ℝ) + 2) * (Φ + 1) * Φ ^ (n + 1) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have step : K * (y * (x + y) ^ (n + 1)) ≤
      K * ((Φ + 1) ^ n * ((Φ + 1) + ((n : ℝ) + 1)) / ((n : ℝ) + 2) * (y * y ^ (n + 1)) +
      ((n : ℝ) + 1) * (Φ + 1) ^ n / (((n : ℝ) + 2) * Φ ^ (n + 1)) * (x * x ^ (n + 1))) := by
    have A' := mul_le_mul_of_nonneg_left A (pow_nonneg hΦ.le (n + 1))
    have Cv' := mul_le_mul_of_nonneg_left Cv hn1
    calc K * (y * (x + y) ^ (n + 1))
        = Φ ^ (n + 1) * (((n : ℝ) + 1 + 1) * ((Φ + 1) * y) * (x + y) ^ (n + 1)) := by
          rw [hK]; ring
      _ ≤ Φ ^ (n + 1) * (((Φ + 1) * y) ^ (n + 1 + 1) + ((n : ℝ) + 1) * (x + y) ^ (n + 1 + 1)) := by
          linarith [A']
      _ = Φ ^ (n + 1) * ((Φ + 1) * y) ^ (n + 1 + 1) +
            ((n : ℝ) + 1) * (Φ ^ (n + 1) * (x + y) ^ (n + 1 + 1)) := by ring
      _ ≤ Φ ^ (n + 1) * ((Φ + 1) * y) ^ (n + 1 + 1) +
            ((n : ℝ) + 1) * (Φ ^ (n + 1) * (Φ + 1) ^ (n + 1) * y ^ (n + 1 + 1) +
              (Φ + 1) ^ (n + 1) * x ^ (n + 1 + 1)) := by linarith
      _ = K * ((Φ + 1) ^ n * ((Φ + 1) + ((n : ℝ) + 1)) / ((n : ℝ) + 2) * (y * y ^ (n + 1)) +
            ((n : ℝ) + 1) * (Φ + 1) ^ n / (((n : ℝ) + 2) * Φ ^ (n + 1)) * (x * x ^ (n + 1))) := by
          have hΦ' : Φ ≠ 0 := hΦ.ne'
          have hn2' : (n : ℝ) + 2 ≠ 0 := hn2.ne'
          rw [hK]
          simp only [mul_pow]
          field_simp
          try ring
  exact le_of_mul_le_mul_left step hK0

/-- Lower-degree version obtained from the top-degree one. -/
theorem base (d j : ℕ) (hj : j ≤ d) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (D : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y * (x + y) ^ d ≤ l * (y * y ^ d) + m * (x * x ^ d))
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y * (x + y) ^ j ≤ l * (y * y ^ j) + m * (x * x ^ j) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = j + e := ⟨d - j, by omega⟩
  rcases (show (0 : ℝ) ≤ x + y by linarith).lt_or_eq with hw | hw
  · have D' := D x y hx hy
    have hyw : y ^ e ≤ (x + y) ^ e := pow_le_pow_left₀ hy (by linarith) e
    have hxw : x ^ e ≤ (x + y) ^ e := pow_le_pow_left₀ hx (by linarith) e
    have a1 : y * y ^ (j + e) ≤ y * y ^ j * (x + y) ^ e := by
      rw [pow_add, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hyw (by positivity)
    have a2 : x * x ^ (j + e) ≤ x * x ^ j * (x + y) ^ e := by
      rw [pow_add, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hxw (by positivity)
    have b1 := mul_le_mul_of_nonneg_left a1 hl
    have b2 := mul_le_mul_of_nonneg_left a2 hm
    have step : (x + y) ^ e * (y * (x + y) ^ j) ≤
        (x + y) ^ e * (l * (y * y ^ j) + m * (x * x ^ j)) := by
      calc (x + y) ^ e * (y * (x + y) ^ j) = y * (x + y) ^ (j + e) := by ring
        _ ≤ l * (y * y ^ (j + e)) + m * (x * x ^ (j + e)) := D'
        _ ≤ l * (y * y ^ j * (x + y) ^ e) + m * (x * x ^ j * (x + y) ^ e) := by linarith
        _ = (x + y) ^ e * (l * (y * y ^ j) + m * (x * x ^ j)) := by ring
    exact le_of_mul_le_mul_left step (pow_pos hw e)
  · have hy0 : y = 0 := by linarith
    have hx0 : x = 0 := by linarith
    subst hy0
    subst hx0
    simp

/-- Monomial version with the extra variable `z`, by binomial expansion in `z`. -/
theorem monoL (d k : ℕ) (hk : k ≤ d) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (D : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y * (x + y) ^ d ≤ l * (y * y ^ d) + m * (x * x ^ d))
    (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    y * (z + x + y) ^ k ≤ l * y * (z + y) ^ k + m * x * (z + x) ^ k := by
  have e1 : z + x + y = z + (x + y) := by ring
  rw [e1, add_pow z (x + y) k, add_pow z y k, add_pow z x k, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hb := base d (k - i) (by omega) l m hl hm D x y hx hy
  have hzc : 0 ≤ z ^ i * ((k.choose i : ℕ) : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hb hzc
  calc y * (z ^ i * (x + y) ^ (k - i) * ((k.choose i : ℕ) : ℝ))
      = z ^ i * ((k.choose i : ℕ) : ℝ) * (y * (x + y) ^ (k - i)) := by ring
    _ ≤ z ^ i * ((k.choose i : ℕ) : ℝ) * (l * (y * y ^ (k - i)) + m * (x * x ^ (k - i))) := this
    _ = l * y * (z ^ i * y ^ (k - i) * ((k.choose i : ℕ) : ℝ)) +
          m * x * (z ^ i * x ^ (k - i) * ((k.choose i : ℕ) : ℝ)) := by ring

/-- Polynomial version. -/
theorem polyL (d : ℕ) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (D : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y * (x + y) ^ d ≤ l * (y * y ^ d) + m * (x * x ^ d))
    (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (f : Polynomial ℝ) (hf : IsPd d f) :
    y * f.eval (z + x + y) ≤ l * y * f.eval (z + y) + m * x * f.eval (z + x) := by
  have hlt : f.natDegree < d + 1 := Nat.lt_succ_of_le hf.1
  simp only [Polynomial.eval_eq_sum_range' hlt]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hmo := monoL d k hkd l m hl hm D x y z hx hy hz
  have hc := hf.2 k
  have := mul_le_mul_of_nonneg_left hmo hc
  calc y * (f.coeff k * (z + x + y) ^ k) = f.coeff k * (y * (z + x + y) ^ k) := by ring
    _ ≤ f.coeff k * (l * y * (z + y) ^ k + m * x * (z + x) ^ k) := this
    _ = l * y * (f.coeff k * (z + y) ^ k) + m * x * (f.coeff k * (z + x) ^ k) := by ring

theorem root_exists (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ ρ * (r + 1) ^ N = r ^ (N + 1) := by
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ρ * 2 ^ N + 1 := ⟨_, rfl⟩
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hX0 : 0 ≤ X := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) (Set.Icc 0 X) := by
    fun_prop
  have hiv := intermediate_value_Icc hX0 hcont
  have hg0 : (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) 0 = -ρ := by simp
  have hgX : 0 ≤ (fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) X := by
    show 0 ≤ X ^ (N + 1) - ρ * (X + 1) ^ N
    have h1 : (X + 1) ^ N ≤ (2 * X) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    have hXN : 0 < X ^ N := by positivity
    have h3 : ρ * 2 ^ N ≤ X := by rw [hX]; linarith
    have h4 : ρ * 2 ^ N * X ^ N ≤ X * X ^ N := mul_le_mul_of_nonneg_right h3 hXN.le
    have h5 := mul_le_mul_of_nonneg_left h1 hρ.le
    rw [pow_succ]
    linarith
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) 0)
      ((fun t : ℝ => t ^ (N + 1) - ρ * (t + 1) ^ N) X) := by
    rw [hg0]; exact ⟨by linarith, hgX⟩
  obtain ⟨r, ⟨hr0, _⟩, hr⟩ := hiv hmem
  have hr' : r ^ (N + 1) - ρ * (r + 1) ^ N = 0 := hr
  refine ⟨r, ?_, by linarith⟩
  rcases hr0.lt_or_eq with h | h
  · exact h
  · subst h
    rw [zero_pow (show N + 1 ≠ 0 by omega), zero_add, one_pow] at hr'
    linarith

theorem strict_mono_aux (N : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    a ^ (N + 1) * (b + 1) ^ N < b ^ (N + 1) * (a + 1) ^ N := by
  have hb : 0 < b := by linarith
  have h1 : a * (b + 1) ≤ b * (a + 1) := by nlinarith
  have h2 : (a * (b + 1)) ^ N ≤ (b * (a + 1)) ^ N := pow_le_pow_left₀ (by positivity) h1 N
  have h3 : 0 < (b * (a + 1)) ^ N := by positivity
  calc a ^ (N + 1) * (b + 1) ^ N = a * (a * (b + 1)) ^ N := by rw [mul_pow]; ring
    _ ≤ a * (b * (a + 1)) ^ N := mul_le_mul_of_nonneg_left h2 ha.le
    _ < b * (b * (a + 1)) ^ N := mul_lt_mul_of_pos_right hab h3
    _ = b ^ (N + 1) * (a + 1) ^ N := by rw [mul_pow]; ring

theorem root_unique (N : ℕ) (ρ : ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hra : ρ * (a + 1) ^ N = a ^ (N + 1)) (hrb : ρ * (b + 1) ^ N = b ^ (N + 1)) : a = b := by
  have key : a ^ (N + 1) * (b + 1) ^ N = b ^ (N + 1) * (a + 1) ^ N := by
    rw [← hra, ← hrb]; ring
  rcases lt_trichotomy a b with h | h | h
  · have := strict_mono_aux N a b ha h; linarith
  · exact h
  · have := strict_mono_aux N b a hb h; linarith

theorem genGolden_eq (N : ℕ) (ρ r : ℝ) (hr : 0 < r) (hroot : ρ * (r + 1) ^ N = r ^ (N + 1)) :
    genGolden N ρ = r := by
  unfold genGolden
  have hset : {x : ℝ | 0 < x ∧ ρ * (x + 1) ^ N = x ^ (N + 1)} = {r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxr⟩
      exact root_unique N ρ x r hx hr hxr hroot
    · rintro rfl
      exact ⟨hr, hroot⟩
  rw [hset, csSup_singleton]

end Aux_WCBR_l2

open WeightedCongestionBR Aux_WCBR_l2 in
theorem solution (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    IsGLB (smoothSet d ρ) (genGolden d ρ ^ (d + 1)) ∧
      genGolden d ρ ^ (d + 1) ∈ smoothSet d ρ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨r, hr0, hroot⟩ := root_exists (n + 1) ρ hρ0
  rw [genGolden_eq (n + 1) ρ r hr0 hroot]
  have hP : 0 < r + 1 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (r + 1) ^ n * ((r + 1) + ((n : ℝ) + 1)) / ((n : ℝ) + 2) :=
    ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((n : ℝ) + 1) * (r + 1) ^ n / (((n : ℝ) + 2) * r ^ (n + 1)) :=
    ⟨_, rfl⟩
  have hl0 : 0 ≤ l := by rw [hl]; positivity
  have hm0 : 0 < m := by rw [hm]; positivity
  have hsum : l + m * r ^ (n + 1 + 1) = (r + 1) ^ (n + 1) := by
    have hr' : r ≠ 0 := hr0.ne'
    have hn2' : (n : ℝ) + 2 ≠ 0 := hn2.ne'
    rw [hl, hm]
    field_simp
    try ring
  have hρ' : ρ = r ^ (n + 1 + 1) / (r + 1) ^ (n + 1) := by
    rw [eq_div_iff (show (r + 1) ^ (n + 1) ≠ 0 by positivity)]
    exact hroot
  have hmρ : m * ρ = ((n : ℝ) + 1) * r / (((n : ℝ) + 2) * (r + 1)) := by
    have hr' : r ≠ 0 := hr0.ne'
    have hn2' : (n : ℝ) + 2 ≠ 0 := hn2.ne'
    have hP' : r + 1 ≠ 0 := hP.ne'
    rw [hm, hρ']
    field_simp
    try ring
  have hmρ1 : m * ρ < 1 := by
    rw [hmρ, div_lt_one (show (0:ℝ) < ((n : ℝ) + 2) * (r + 1) by positivity)]
    nlinarith
  have hmem : r ^ (n + 1 + 1) ∈ smoothSet (n + 1) ρ := by
    refine ⟨l, m, hm0, ?_, ?_, ?_⟩
    · rw [lt_div_iff₀ hρ0]; exact hmρ1
    · intro x y z hx hy hz f hf
      have D : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
          y * (x + y) ^ (n + 1) ≤ l * (y * y ^ (n + 1)) + m * (x * x ^ (n + 1)) := by
        intro x y hx hy
        rw [hl, hm]
        exact degD n r hr0 x y hx hy
      exact polyL (n + 1) l m hl0 hm0.le D x y z hx hy hz f hf
    · have hne : 1 - m * ρ ≠ 0 := by linarith
      rw [eq_div_iff hne]
      linear_combination (-ρ) * hsum - hroot
  refine ⟨⟨?_, fun b hb => hb hmem⟩, hmem⟩
  rintro b ⟨lam, μ, hμ0, hμρ, hineq, rfl⟩
  have hμρ' : μ * ρ < 1 := (lt_div_iff₀ hρ0).mp hμρ
  have hpd : IsPd (n + 1) ((Polynomial.X : Polynomial ℝ) ^ (n + 1)) := by
    refine ⟨by rw [Polynomial.natDegree_X_pow], fun j => ?_⟩
    rw [Polynomial.coeff_X_pow]
    split_ifs <;> norm_num
  have h := hineq r 1 0 hr0.le zero_le_one le_rfl _ hpd
  simp only [Polynomial.eval_pow, Polynomial.eval_X, zero_add, one_mul, mul_one, one_pow] at h
  rw [le_div_iff₀ (show (0:ℝ) < 1 - μ * ρ by linarith)]
  have e : r ^ (n + 1 + 1) = r * r ^ (n + 1) := by ring
  rw [e] at hroot ⊢
  have h2 := mul_le_mul_of_nonneg_left h hρ0.le
  linarith [h2, hroot]
