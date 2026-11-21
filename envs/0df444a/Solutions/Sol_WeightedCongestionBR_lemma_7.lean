-- Prove2me | solution 1 for WeightedCongestionBR.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:11:00.640445+00:00
-- url     : https://prove2.me/submissions/55df4bba-d640-418b-bc7c-cd0405d0aa81

import Mathlib
import Definitions.Def_WeightedCongestionBR_genGolden
import Definitions.Def_WeightedCongestionBR_PoASet
import Definitions.Def_WeightedCongestionBR_alphaC
import Definitions.Def_WeightedCongestionBR_pConst
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency


namespace Aux_WCBR_t1

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
    (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (f : Polynomial ℝ) (hf : f.natDegree ≤ d ∧ ∀ j, 0 ≤ f.coeff j) :
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


/-- A feasible smoothness pair attaining `Φ^(d+1)`. -/
theorem feasible (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    ∃ l m : ℝ, 0 ≤ l ∧ 0 < m ∧ m * ρ < 1 ∧
      (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → ∀ f : Polynomial ℝ,
        (f.natDegree ≤ d ∧ ∀ j, 0 ≤ f.coeff j) →
        y * f.eval (z + x + y) ≤ l * y * f.eval (z + y) + m * x * f.eval (z + x)) ∧
      genGolden d ρ ^ (d + 1) = l * ρ / (1 - m * ρ) := by
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
  refine ⟨l, m, hl0, hm0, hmρ1, ?_, ?_⟩
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

noncomputable def gl {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) : ℝ :=
  ∑ u ∈ R, if e ∈ (s u).val then (G.demand u : ℝ) else 0

theorem load_eq {n r : ℕ} (G : Game n r) (s : G.Profile) (e : Fin r) :
    ((load G s e : ℝ≥0) : ℝ) = gl G s Finset.univ e := by
  unfold load gl
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> simp

theorem gl_split {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    gl G s Finset.univ e = gl G s Rᶜ e + gl G s R e := by
  unfold gl
  rw [← Finset.sum_add_sum_compl R]
  ring

theorem gl_nonneg {n r : ℕ} (G : Game n r) (s : G.Profile) (R : Finset (Fin n)) (e : Fin r) :
    0 ≤ gl G s R e := by
  unfold gl
  refine Finset.sum_nonneg (fun u _ => ?_)
  split_ifs
  · exact NNReal.coe_nonneg _
  · exact le_rfl

theorem eval_mono (P : Polynomial ℝ) (hP : ∀ j, 0 ≤ P.coeff j) (a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) : P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab i) (hP i)

theorem swap {n r : ℕ} (G : Game n r) (t : G.Profile) (R : Finset (Fin n)) (F : Fin r → ℝ) :
    ∑ u ∈ R, ∑ e ∈ (t u).val, (G.demand u : ℝ) * F e = ∑ e : Fin r, gl G t R e * F e := by
  unfold gl
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem_eq]

theorem gl_update_le {n r : ℕ} (G : Game n r) (s : G.Profile) (u : Fin n) (t : G.Strategy u)
    (e : Fin r) (he : e ∈ t.val) :
    gl G (Function.update s u t) Finset.univ e ≤ gl G s Finset.univ e + G.demand u := by
  unfold gl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u), ← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
  have hS : ∑ v ∈ Finset.univ.erase u,
      (if e ∈ (Function.update s u t v).val then (G.demand v : ℝ) else 0) =
      ∑ v ∈ Finset.univ.erase u, (if e ∈ (s v).val then (G.demand v : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  rw [hS, Function.update_self, if_pos he]
  have h0 : 0 ≤ (if e ∈ (s u).val then (G.demand u : ℝ) else 0) := by
    split_ifs
    · exact NNReal.coe_nonneg _
    · exact le_rfl
  linarith

theorem demand_le_gl {n r : ℕ} (G : Game n r) (t : G.Profile) (R : Finset (Fin n)) (u : Fin n)
    (hu : u ∈ R) (e : Fin r) (he : e ∈ (t u).val) : (G.demand u : ℝ) ≤ gl G t R e := by
  unfold gl
  have hle := Finset.single_le_sum (f := fun v => if e ∈ (t v).val then (G.demand v : ℝ) else 0)
    (fun v _ => by
      show 0 ≤ (if e ∈ (t v).val then (G.demand v : ℝ) else 0)
      split_ifs
      · exact NNReal.coe_nonneg _
      · exact le_rfl) hu
  simp only [he, ↓reduceIte] at hle
  exact hle

theorem groupCost_eq {n r : ℕ} (G : Game n r) (P : Fin r → Polynomial ℝ)
    (hcost : ∀ e (x : ℝ≥0), G.cost e x = (P e).eval (x : ℝ)) (R : Finset (Fin n)) (t : G.Profile) :
    groupCost G R t = ∑ e : Fin r, gl G t R e * (P e).eval (gl G t Rᶜ e + gl G t R e) := by
  unfold groupCost privateCost
  refine (swap G t R (fun e => G.cost e (load G t e))).trans ?_
  refine Finset.sum_congr rfl (fun e _ => ?_)
  show gl G t R e * G.cost e (load G t e) = _
  rw [hcost e, load_eq, gl_split G t R e]

theorem mainL {n r : ℕ} (G : Game n r) (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ)
    (hG : CongestionApproxPNE.IsPolyGame d G) (R : Finset (Fin n)) (s sStar : G.Profile)
    (hs : IsGroupEq G ρ R s) (hout : ∀ u ∉ R, s u = sStar u) :
    groupCost G R s ≤ genGolden d ρ ^ (d + 1) * groupCost G R sStar := by
  choose P hdeg hcoef hcost using hG
  obtain ⟨l, m, hl0, hm0, hmρ, hsm, hΦ⟩ := feasible d ρ hd hρ
  have hρ0 : 0 < ρ := by linarith
  have hz : ∀ e, gl G sStar Rᶜ e = gl G s Rᶜ e := by
    intro e
    unfold gl
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [hout v (Finset.mem_compl.mp hv)]
  have hCs := groupCost_eq G P hcost R s
  have hCst := groupCost_eq G P hcost R sStar
  simp only [hz] at hCst
  -- equilibrium step
  have heq : groupCost G R s ≤ ρ * ∑ e : Fin r, gl G sStar R e *
      (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) := by
    have h1 : ∀ u ∈ R, privateCost G s u ≤ ρ * ∑ e ∈ (sStar u).val, (G.demand u : ℝ) *
        (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) := by
      intro u hu
      refine le_trans (hs u hu (sStar u)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hρ0.le
      unfold privateCost
      rw [Function.update_self]
      refine Finset.sum_le_sum (fun e he => ?_)
      rw [hcost e, load_eq]
      refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
      refine eval_mono (P e) (hcoef e) _ _ (gl_nonneg G _ _ e) ?_
      have a1 := gl_update_le G s u (sStar u) e he
      have a2 := demand_le_gl G sStar R u hu e he
      rw [gl_split G s R e] at a1
      linarith
    unfold groupCost
    calc ∑ u ∈ R, privateCost G s u
        ≤ ∑ u ∈ R, ρ * ∑ e ∈ (sStar u).val, (G.demand u : ℝ) *
            (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) := Finset.sum_le_sum h1
      _ = ρ * ∑ e : Fin r, gl G sStar R e *
            (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) := by
          rw [← Finset.mul_sum]
          congr 1
          exact swap G sStar R _
  -- smoothness step
  have hsmooth : ∑ e : Fin r, gl G sStar R e *
      (P e).eval (gl G s Rᶜ e + gl G s R e + gl G sStar R e) ≤
      l * groupCost G R sStar + m * groupCost G R s := by
    rw [hCs, hCst, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun e _ => ?_)
    have := hsm (gl G s R e) (gl G sStar R e) (gl G s Rᶜ e) (gl_nonneg G _ _ e) (gl_nonneg G _ _ e)
      (gl_nonneg G _ _ e) (P e) ⟨hdeg e, hcoef e⟩
    linarith
  have hfin : groupCost G R s ≤ ρ * (l * groupCost G R sStar + m * groupCost G R s) :=
    le_trans heq (mul_le_mul_of_nonneg_left hsmooth hρ0.le)
  rw [hΦ, div_mul_eq_mul_div, le_div_iff₀ (show (0:ℝ) < 1 - m * ρ by linarith)]
  linarith [hfin]

theorem thm1 (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) :
    ∀ q ∈ PoASet d ρ, q ≤ genGolden d ρ ^ (d + 1) := by
  rintro q ⟨n, r, G, hG, s, sStar, hs, _, hpos, rfl⟩
  have h1 := mainL G d ρ hd hρ hG Finset.univ s sStar hs (fun u hu => absurd (Finset.mem_univ u) hu)
  rw [div_le_iff₀ hpos]
  exact h1

end Aux_WCBR_t1


namespace Aux_WCBR_t2

open WeightedCongestionBR

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



theorem wpow (q : ℝ) (i d : ℕ) : (q ^ i) ^ (d + 1) = (q ^ (d + 1)) ^ i := by
  rw [← pow_mul, ← pow_mul, mul_comm]

/-- The lower-bound game: players `0..M` on a path of resources `0..M+1`. -/
noncomputable def LB (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) : Game (M + 1) (M + 1 + 1) where
  players_pos := Nat.succ_pos M
  facilities_pos := Nat.succ_pos (M + 1)
  strategies := fun i => {{Fin.castSucc i}, {Fin.succ i}}
  strategies_nonempty := fun i =>
    ⟨{Fin.succ i}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  demand := fun i => ⟨Φ⁻¹ ^ (i : ℕ), pow_nonneg (inv_nonneg.mpr hΦ.le) _⟩
  demand_pos := fun i => NNReal.coe_pos.mp (pow_pos (inv_pos.mpr hΦ) _)
  cost := fun k x => K ^ (max (k : ℕ) 1) * (x : ℝ) ^ d

noncomputable def sR (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) : (LB M d Φ K hΦ).Profile :=
  fun i => ⟨{Fin.succ i}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

noncomputable def sL (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) : (LB M d Φ K hΦ).Profile :=
  fun i => ⟨{Fin.castSucc i}, Finset.mem_insert_self _ _⟩

noncomputable def Lr (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile)
    (e : Fin (M + 1 + 1)) : ℝ :=
  ∑ j : Fin (M + 1), if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0

theorem load_eq' (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile)
    (e : Fin (M + 1 + 1)) :
    ((load (LB M d Φ K hΦ) t e : ℝ≥0) : ℝ) = Lr M d Φ K hΦ t e := by
  unfold load Lr
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rfl
  · simp

theorem pc_eq (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile) (u : Fin (M + 1)) :
    privateCost (LB M d Φ K hΦ) t u = ∑ f ∈ (t u).val,
      Φ⁻¹ ^ (u : ℕ) * (K ^ (max (f : ℕ) 1) * (Lr M d Φ K hΦ t f) ^ d) := by
  unfold privateCost
  refine Finset.sum_congr rfl (fun f _ => ?_)
  show Φ⁻¹ ^ (u : ℕ) * (K ^ (max (f : ℕ) 1) * ((load (LB M d Φ K hΦ) t f : ℝ≥0) : ℝ) ^ d) = _
  rw [load_eq']

theorem L_ge_one (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile)
    (j : Fin (M + 1)) (e : Fin (M + 1 + 1)) (he : e ∈ (t j).val) :
    Φ⁻¹ ^ (j : ℕ) ≤ Lr M d Φ K hΦ t e := by
  unfold Lr
  have hle := Finset.single_le_sum
    (f := fun j : Fin (M + 1) => if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0)
    (fun j _ => by
      show 0 ≤ (if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0)
      split_ifs
      · exact pow_nonneg (inv_nonneg.mpr hΦ.le) _
      · exact le_rfl) (Finset.mem_univ j)
  simp only [he, ↓reduceIte] at hle
  exact hle

theorem L_ge_two (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (t : (LB M d Φ K hΦ).Profile)
    (j j' : Fin (M + 1)) (hjj : j ≠ j') (e : Fin (M + 1 + 1)) (he : e ∈ (t j).val)
    (he' : e ∈ (t j').val) :
    Φ⁻¹ ^ (j : ℕ) + Φ⁻¹ ^ (j' : ℕ) ≤ Lr M d Φ K hΦ t e := by
  unfold Lr
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {j, j'})
    (f := fun j : Fin (M + 1) => if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0)
    (fun j _ _ => by
      show 0 ≤ (if e ∈ (t j).val then Φ⁻¹ ^ (j : ℕ) else 0)
      split_ifs
      · exact pow_nonneg (inv_nonneg.mpr hΦ.le) _
      · exact le_rfl)
  rw [Finset.sum_pair hjj] at hle
  simp only [he, he', ↓reduceIte] at hle
  exact hle

theorem L_sR (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (i : Fin (M + 1)) :
    Lr M d Φ K hΦ (sR M d Φ K hΦ) (Fin.succ i) = Φ⁻¹ ^ (i : ℕ) := by
  simp [Lr, sR]

theorem L_sL (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (i : Fin (M + 1)) :
    Lr M d Φ K hΦ (sL M d Φ K hΦ) (Fin.castSucc i) = Φ⁻¹ ^ (i : ℕ) := by
  simp [Lr, sL]

theorem pc_sR (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hKq : K * Φ⁻¹ ^ (d + 1) = 1) (i : Fin (M + 1)) :
    privateCost (LB M d Φ K hΦ) (sR M d Φ K hΦ) i = K := by
  rw [pc_eq]
  have hv : ((sR M d Φ K hΦ) i).val = {Fin.succ i} := rfl
  rw [hv, Finset.sum_singleton, L_sR, Fin.val_succ, max_eq_left (by omega : 1 ≤ (i : ℕ) + 1)]
  calc Φ⁻¹ ^ (i : ℕ) * (K ^ ((i : ℕ) + 1) * (Φ⁻¹ ^ (i : ℕ)) ^ d)
      = K * (K * Φ⁻¹ ^ (d + 1)) ^ (i : ℕ) := by rw [mul_pow, ← wpow]; ring
    _ = K := by rw [hKq, one_pow, mul_one]

theorem pc_sL (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hKq : K * Φ⁻¹ ^ (d + 1) = 1) (i : Fin (M + 1)) :
    privateCost (LB M d Φ K hΦ) (sL M d Φ K hΦ) i = if (i : ℕ) = 0 then K else 1 := by
  rw [pc_eq]
  have hv : ((sL M d Φ K hΦ) i).val = {Fin.castSucc i} := rfl
  rw [hv, Finset.sum_singleton, L_sL, Fin.coe_castSucc]
  split_ifs with h
  · rw [h]; simp
  · rw [max_eq_left (by omega : 1 ≤ (i : ℕ))]
    calc Φ⁻¹ ^ (i : ℕ) * (K ^ (i : ℕ) * (Φ⁻¹ ^ (i : ℕ)) ^ d)
        = (K * Φ⁻¹ ^ (d + 1)) ^ (i : ℕ) := by rw [mul_pow, ← wpow]; ring
      _ = 1 := by rw [hKq, one_pow]

theorem pc_pos (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hK : 0 < K) (t : (LB M d Φ K hΦ).Profile)
    (u : Fin (M + 1)) : 0 < privateCost (LB M d Φ K hΦ) t u := by
  rw [pc_eq]
  have hmem : (t u).val ∈ ({{Fin.castSucc u}, {Fin.succ u}} : Finset (Finset (Fin (M + 1 + 1)))) :=
    (t u).property
  have hne : (t u).val.Nonempty := by
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h]; exact Finset.singleton_nonempty _
    · rw [Finset.mem_singleton.mp h]; exact Finset.singleton_nonempty _
  refine Finset.sum_pos (fun f hf => ?_) hne
  have hq : 0 < Φ⁻¹ ^ (u : ℕ) := pow_pos (inv_pos.mpr hΦ) _
  have hL := L_ge_one M d Φ K hΦ t u f hf
  have hL0 : 0 < Lr M d Φ K hΦ t f := lt_of_lt_of_le hq hL
  positivity

theorem gc_pos (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hK : 0 < K) (t : (LB M d Φ K hΦ).Profile) :
    0 < groupCost (LB M d Φ K hΦ) Finset.univ t := by
  unfold groupCost
  exact Finset.sum_pos (fun u _ => pc_pos M d Φ K hΦ hK t u) Finset.univ_nonempty

theorem gc_sR (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hKq : K * Φ⁻¹ ^ (d + 1) = 1) :
    groupCost (LB M d Φ K hΦ) Finset.univ (sR M d Φ K hΦ) = ((M : ℝ) + 1) * K := by
  unfold groupCost
  simp only [pc_sR M d Φ K hΦ hKq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

theorem gc_sL (M d : ℕ) (Φ K : ℝ) (hΦ : 0 < Φ) (hKq : K * Φ⁻¹ ^ (d + 1) = 1) :
    groupCost (LB M d Φ K hΦ) Finset.univ (sL M d Φ K hΦ) = K + M := by
  unfold groupCost
  simp only [pc_sL M d Φ K hΦ hKq]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, ↓reduceIte, Nat.add_one_ne_zero]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem isEq (M d : ℕ) (Φ K ρ : ℝ) (hΦ : 0 < Φ) (hK : 0 < K) (hρ : 1 ≤ ρ)
    (hKq : K * Φ⁻¹ ^ (d + 1) = 1) (hroot : ρ * (Φ + 1) ^ d = K) :
    IsGroupEq (LB M d Φ K hΦ) ρ Finset.univ (sR M d Φ K hΦ) := by
  intro u _ t
  have hmem : t.val ∈ ({{Fin.castSucc u}, {Fin.succ u}} : Finset (Finset (Fin (M + 1 + 1)))) :=
    t.property
  have hq0 : 0 < Φ⁻¹ := inv_pos.mpr hΦ
  rcases Finset.mem_insert.mp hmem with hL | hR
  · have hu_mem : Fin.castSucc u ∈ ((Function.update (sR M d Φ K hΦ) u t) u).val := by
      rw [Function.update_self, hL]; exact Finset.mem_singleton_self _
    have hL1 := L_ge_one M d Φ K hΦ (Function.update (sR M d Φ K hΦ) u t) u _ hu_mem
    obtain ⟨L, hLdef⟩ : ∃ L, L = Lr M d Φ K hΦ (Function.update (sR M d Φ K hΦ) u t)
        (Fin.castSucc u) := ⟨_, rfl⟩
    rw [← hLdef] at hL1
    rw [pc_sR M d Φ K hΦ hKq, pc_eq, Function.update_self, hL, Finset.sum_singleton,
      Fin.coe_castSucc, ← hLdef]
    rcases Nat.eq_zero_or_pos (u : ℕ) with h0 | hpos
    · rw [h0] at hL1 ⊢
      norm_num at hL1 ⊢
      have hLd : 1 ≤ L ^ d := one_le_pow₀ hL1
      have a1 : K ≤ K * L ^ d := le_mul_of_one_le_right hK.le hLd
      have a2 : 0 ≤ K * L ^ d := by linarith
      nlinarith
    · obtain ⟨k, hk⟩ : ∃ k, (u : ℕ) = k + 1 := ⟨(u : ℕ) - 1, by omega⟩
      have hkN : k < M + 1 := by have := u.isLt; omega
      obtain ⟨j', hj'⟩ : ∃ j' : Fin (M + 1), j' = ⟨k, hkN⟩ := ⟨_, rfl⟩
      have hj'v : (j' : ℕ) = k := by rw [hj']
      have hjne : u ≠ j' := by
        intro h
        have := congrArg Fin.val h
        omega
      have hj'mem : Fin.castSucc u ∈ ((Function.update (sR M d Φ K hΦ) u t) j').val := by
        rw [Function.update_of_ne (Ne.symm hjne)]
        show Fin.castSucc u ∈ ({Fin.succ j'} : Finset (Fin (M + 1 + 1)))
        rw [Finset.mem_singleton, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ, hj'v, hk]
      have hL2 := L_ge_two M d Φ K hΦ (Function.update (sR M d Φ K hΦ) u t) u j' hjne _ hu_mem
        hj'mem
      rw [← hLdef, hj'v] at hL2
      rw [max_eq_left (by omega : 1 ≤ (u : ℕ))]
      have hqk : Φ⁻¹ ^ k = Φ * Φ⁻¹ ^ (u : ℕ) := by
        rw [hk, pow_succ, ← mul_assoc, mul_comm Φ, mul_assoc, mul_inv_cancel₀ hΦ.ne', mul_one]
      rw [hqk] at hL2
      have hb : Φ⁻¹ ^ (u : ℕ) * (Φ + 1) ≤ L := by linarith
      have hb' : (Φ⁻¹ ^ (u : ℕ)) ^ d * (Φ + 1) ^ d ≤ L ^ d := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hb d
      have hval : Φ⁻¹ ^ (u : ℕ) * (K ^ (u : ℕ) * ((Φ⁻¹ ^ (u : ℕ)) ^ d * (Φ + 1) ^ d)) =
          (Φ + 1) ^ d := by
        calc Φ⁻¹ ^ (u : ℕ) * (K ^ (u : ℕ) * ((Φ⁻¹ ^ (u : ℕ)) ^ d * (Φ + 1) ^ d))
            = (K * Φ⁻¹ ^ (d + 1)) ^ (u : ℕ) * (Φ + 1) ^ d := by rw [mul_pow, ← wpow]; ring
          _ = (Φ + 1) ^ d := by rw [hKq, one_pow, one_mul]
      have hmono : Φ⁻¹ ^ (u : ℕ) * (K ^ (u : ℕ) * ((Φ⁻¹ ^ (u : ℕ)) ^ d * (Φ + 1) ^ d)) ≤
          Φ⁻¹ ^ (u : ℕ) * (K ^ (u : ℕ) * L ^ d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hb' (by positivity)
      rw [hval] at hmono
      have := mul_le_mul_of_nonneg_left hmono (by linarith : (0:ℝ) ≤ ρ)
      linarith
  · have hts : t = sR M d Φ K hΦ u := Subtype.ext (Finset.mem_singleton.mp hR)
    rw [hts, Function.update_eq_self]
    have h0 := (pc_pos M d Φ K hΦ hK (sR M d Φ K hΦ) u).le
    nlinarith

theorem thm2 (d : ℕ) (ρ : ℝ) (hd : 1 ≤ d) (hρ : 1 ≤ ρ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n r : ℕ) (G : Game n r), CongestionApproxPNE.IsPolyGame d G ∧
      (∀ u : Fin n, ∀ t ∈ G.strategies u, t.card = 1) ∧
      ∃ s sStar : G.Profile, IsGroupEq G ρ Finset.univ s ∧
        (∀ s' : G.Profile, groupCost G Finset.univ sStar ≤ groupCost G Finset.univ s') ∧
        0 < groupCost G Finset.univ sStar ∧
        genGolden d ρ ^ (d + 1) - ε ≤ groupCost G Finset.univ s / groupCost G Finset.univ sStar := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨Φ, hΦ, hroot⟩ := root_exists d ρ hρ0
  rw [genGolden_eq d ρ Φ hΦ hroot]
  obtain ⟨K, hKdef⟩ : ∃ K, K = Φ ^ (d + 1) := ⟨_, rfl⟩
  rw [← hKdef]
  have hK : 0 < K := by rw [hKdef]; positivity
  have hKq : K * Φ⁻¹ ^ (d + 1) = 1 := by
    rw [hKdef, ← mul_pow, mul_inv_cancel₀ hΦ.ne', one_pow]
  have hroot' : ρ * (Φ + 1) ^ d = K := by rw [hKdef]; exact hroot
  have hK1 : 1 ≤ K := by
    rw [← hroot']
    have : 1 ≤ (Φ + 1) ^ d := one_le_pow₀ (by linarith)
    nlinarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = Nat.ceil (K ^ 2 / ε) := ⟨_, rfl⟩
  have hMb : K ^ 2 / ε ≤ M := by rw [hM]; exact Nat.le_ceil _
  have hMb' : K ^ 2 ≤ ε * M := by
    rw [div_le_iff₀ hε] at hMb; linarith
  refine ⟨M + 1, M + 1 + 1, LB M d Φ K hΦ, ?_, ?_, ?_⟩
  · intro f
    refine ⟨Polynomial.C (K ^ (max (f : ℕ) 1)) * Polynomial.X ^ d,
      Polynomial.natDegree_C_mul_X_pow_le _ _, fun j => ?_, fun x => ?_⟩
    · rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · positivity
      · exact le_rfl
    · simp [LB]
  · intro u t ht
    have hmem : t ∈ ({{Fin.castSucc u}, {Fin.succ u}} : Finset (Finset (Fin (M + 1 + 1)))) := ht
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h, Finset.card_singleton]
    · rw [Finset.mem_singleton.mp h, Finset.card_singleton]
  · obtain ⟨sStar, _, hmin⟩ := Finset.exists_min_image Finset.univ
      (fun t => groupCost (LB M d Φ K hΦ) Finset.univ t) ⟨sR M d Φ K hΦ, Finset.mem_univ _⟩
    refine ⟨sR M d Φ K hΦ, sStar, isEq M d Φ K ρ hΦ hK hρ hKq hroot',
      fun s' => hmin s' (Finset.mem_univ _), gc_pos M d Φ K hΦ hK sStar, ?_⟩
    have hopt : groupCost (LB M d Φ K hΦ) Finset.univ sStar ≤
        groupCost (LB M d Φ K hΦ) Finset.univ (sL M d Φ K hΦ) := hmin _ (Finset.mem_univ _)
    have hpos := gc_pos M d Φ K hΦ hK sStar
    rw [gc_sL M d Φ K hΦ hKq] at hopt
    rw [gc_sR M d Φ K hΦ hKq]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h1 : ((M : ℝ) + 1) * K / (K + M) ≤
        ((M : ℝ) + 1) * K / groupCost (LB M d Φ K hΦ) Finset.univ sStar :=
      div_le_div_of_nonneg_left (by positivity) hpos hopt
    have h2 : K - ε ≤ ((M : ℝ) + 1) * K / (K + M) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith

end Aux_WCBR_t2

namespace Aux_WCBR_l7

open WeightedCongestionBR

theorem phi_le (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ (d : ℝ) + 2) :
    genGolden d ρ ≤ 4 * (d : ℝ) := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨Φ, hΦ, hroot⟩ := Aux_WCBR_t1.root_exists d ρ hρ0
  rw [Aux_WCBR_t1.genGolden_eq d ρ Φ hΦ hroot]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 4 * (d : ℝ) := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 < A := by rw [hA]; linarith
  have hB0 : 0 < A + 1 := by linarith
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / (A + 1)) by
    have : 0 ≤ 1 / (A + 1) := by positivity
    have : 1 / (A + 1) ≤ 1 := by rw [div_le_one hB0]; linarith
    linarith) d
  have hBne : A + 1 ≠ 0 := hB0.ne'
  have e1 : (1 : ℝ) + -(1 / (A + 1)) = A / (A + 1) := by
    rw [one_div, eq_div_iff hBne, add_mul, neg_mul, inv_mul_cancel₀ hBne]
    ring
  rw [e1, div_pow] at hb
  have hdB : (d : ℝ) / (A + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ hB0]; rw [hA]; linarith
  have e2 : (1 : ℝ) + (d : ℝ) * -(1 / (A + 1)) = 1 - (d : ℝ) / (A + 1) := by ring
  rw [e2] at hb
  have h34 : (3 : ℝ) / 4 ≤ A ^ d / (A + 1) ^ d := by linarith
  rw [le_div_iff₀ (pow_pos hB0 d)] at h34
  -- ρ (A+1)^d ≤ A^(d+1)
  have hkey : ρ * (A + 1) ^ d ≤ A ^ (d + 1) := by
    have hBd : 0 < (A + 1) ^ d := pow_pos hB0 d
    have h1 : ρ * (A + 1) ^ d ≤ (3 * (d : ℝ)) * (A + 1) ^ d :=
      mul_le_mul_of_nonneg_right (by linarith) hBd.le
    have h2 : (3 * (d : ℝ)) * (A + 1) ^ d ≤ (d : ℝ) * (4 * A ^ d) := by
      have := mul_le_mul_of_nonneg_left h34 (show (0 : ℝ) ≤ d by linarith)
      linarith
    have h3 : (d : ℝ) * (4 * A ^ d) = A ^ (d + 1) := by rw [pow_succ, hA]; ring
    linarith
  by_contra hlt
  push_neg at hlt
  have hsm := Aux_WCBR_t1.strict_mono_aux d A Φ hA0 hlt
  rw [← hroot] at hsm
  have hP : 0 < (Φ + 1) ^ d := pow_pos (by linarith) d
  have : A ^ (d + 1) < ρ * (A + 1) ^ d := by
    have h' : A ^ (d + 1) * (Φ + 1) ^ d < (ρ * (A + 1) ^ d) * (Φ + 1) ^ d := by
      calc A ^ (d + 1) * (Φ + 1) ^ d < ρ * (Φ + 1) ^ d * (A + 1) ^ d := hsm
        _ = (ρ * (A + 1) ^ d) * (Φ + 1) ^ d := by ring
    exact lt_of_mul_lt_mul_right h' hP.le
  linarith

end Aux_WCBR_l7

open WeightedCongestionBR in
theorem solution (d : ℕ) (hd : 1 ≤ d) :
    IsLUB (PoASet d (alphaC d + 1 / pConst d)) (genGolden d (alphaC d + 1 / pConst d) ^ (d + 1)) ∧
      (2 * alphaC d + 1) * alphaC d * genGolden d (alphaC d + 1 / pConst d) ^ (d + 1) ≤
        pConst d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 ≤ pConst d := by
    unfold pConst
    have h4 : (1 : ℝ) ≤ (4 * (d : ℝ)) ^ (d + 1) := one_le_pow₀ (by linarith)
    have h5 : (1 : ℝ) ≤ (2 * (d : ℝ) + 3) * ((d : ℝ) + 1) := by nlinarith
    nlinarith
  have hp0 : 0 < pConst d := by linarith
  have hinv : 0 < 1 / pConst d := by positivity
  have hinv1 : 1 / pConst d ≤ 1 := by rw [div_le_one hp0]; exact hp1
  have hρ1 : 1 ≤ alphaC d + 1 / pConst d := by unfold alphaC; linarith
  have hρ2 : alphaC d + 1 / pConst d ≤ (d : ℝ) + 2 := by unfold alphaC; linarith
  refine ⟨⟨fun q hq => Aux_WCBR_t1.thm1 d _ hd hρ1 q hq, fun b hb => ?_⟩, ?_⟩
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, r, G, hG, _, s, sStar, hs, hmin, hpos, hge⟩ :=
      Aux_WCBR_t2.thm2 d _ hd hρ1 ε hε
    have hmem : groupCost G Finset.univ s / groupCost G Finset.univ sStar ∈
        PoASet d (alphaC d + 1 / pConst d) :=
      ⟨n, r, G, hG, s, sStar, hs, hmin, hpos, rfl⟩
    have := hb hmem
    linarith
  · have hΦ := Aux_WCBR_l7.phi_le d hd _ hρ1 hρ2
    have hρ0 : 0 < alphaC d + 1 / pConst d := by linarith
    obtain ⟨Φ, hΦ0, hroot⟩ := Aux_WCBR_t1.root_exists d _ hρ0
    have hg := Aux_WCBR_t1.genGolden_eq d _ Φ hΦ0 hroot
    rw [hg] at hΦ ⊢
    have hpow : Φ ^ (d + 1) ≤ (4 * (d : ℝ)) ^ (d + 1) := pow_le_pow_left₀ hΦ0.le hΦ (d + 1)
    have hc : 0 ≤ (2 * alphaC d + 1) * alphaC d := by unfold alphaC; positivity
    have := mul_le_mul_of_nonneg_left hpow hc
    calc (2 * alphaC d + 1) * alphaC d * Φ ^ (d + 1)
        ≤ (2 * alphaC d + 1) * alphaC d * (4 * (d : ℝ)) ^ (d + 1) := this
      _ = pConst d := by unfold alphaC pConst; ring
