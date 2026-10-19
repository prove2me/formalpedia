-- Prove2me | solution 2 for RamanujanNotebooks.entry_31_24
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:16:24.91018+00:00
-- url     : https://prove2.me/submissions/2ca7bb1a-5131-4ab9-a5eb-26b0c8f79a4b

import Mathlib
set_option autoImplicit false

open Filter Topology

lemma ram_sin_ne (x : ℝ) (hx0 : x ≠ 0)
    (hx : ∀ k : ℕ, 1 ≤ k → ∀ j : ℤ, x / 2 ^ k ≠ (2 * (j : ℝ) + 1) * (Real.pi / 2))
    (n : ℕ) : Real.sin (x / 2 ^ n) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp h
  have hxm : x = m * Real.pi * 2 ^ n := by
    rw [hm]; field_simp
  have key : ∀ k : ℕ, (2 : ℤ) ^ k ∣ m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      rcases Int.even_or_odd t with ⟨s, hs⟩ | ⟨j, hj⟩
      · exact ⟨s, by rw [ht, hs]; ring⟩
      · exfalso
        apply hx (n + k + 1) (by omega) j
        have : x / 2 ^ (n + k + 1) = t * Real.pi / 2 := by
          rw [hxm, ht]; push_cast; rw [pow_succ, pow_add]; field_simp
        rw [this, hj]; push_cast; ring
  have hm0 : m = 0 := by
    by_contra hne
    have h1 := key m.natAbs
    have h2 : 2 ^ m.natAbs ∣ m.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h1
      simpa [Int.natAbs_pow] using this
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h2
    exact absurd h3 (not_le.mpr Nat.lt_two_pow_self)
  apply hx0
  rw [hxm, hm0]; simp

lemma ram_tan_eq (y : ℝ) (hs : Real.sin y ≠ 0) (hc : Real.cos y ≠ 0) :
    Real.tan y = Real.cos y / Real.sin y - 2 * (Real.cos (2 * y) / Real.sin (2 * y)) := by
  have h := Real.sin_sq_add_cos_sq y
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
  field_simp
  nlinarith [h]

lemma ram_abs_tan_le (t : ℝ) (h : |t| ≤ 1) : |Real.tan t| ≤ 2 * |t| := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  have hc : 1 / 2 ≤ Real.cos t := by
    have := Real.one_sub_sq_div_two_le_cos (x := t)
    linarith
  rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos (by linarith : 0 < Real.cos t),
    div_le_iff₀ (by linarith)]
  have := Real.abs_sin_le_abs (x := t)
  nlinarith [abs_nonneg t, abs_nonneg (Real.sin t)]

lemma ram_norm_le (t : ℝ) (k : ℕ) (h : |t| ≤ 1) :
    ‖Real.tan t / 2 ^ (k + 1)‖ ≤ (1 / 2 : ℝ) ^ k := by
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (k + 1)),
    div_le_iff₀ (by positivity)]
  have h1 := ram_abs_tan_le t h
  have h2 : (1 / 2 : ℝ) ^ k * 2 ^ (k + 1) = 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
  rw [h2]
  linarith

theorem solution (x : ℝ) (hx0 : x ≠ 0)
    (hx : ∀ k : ℕ, 1 ≤ k → ∀ j : ℤ, x / 2 ^ k ≠ (2 * (j : ℝ) + 1) * (Real.pi / 2)) :
    HasSum (fun k : ℕ => Real.tan (x / 2 ^ (k + 1)) / 2 ^ (k + 1))
      (1 / x - Real.cos x / Real.sin x) := by
  have hs := ram_sin_ne x hx0 hx
  have hc : ∀ k : ℕ, 1 ≤ k → Real.cos (x / 2 ^ k) ≠ 0 := by
    intro k hk h
    obtain ⟨j, hj⟩ := Real.cos_eq_zero_iff.mp h
    apply hx k hk j
    rw [hj]; ring
  have ht0 : Tendsto (fun n : ℕ => x / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  set c : ℕ → ℝ := fun k => Real.cos (x / 2 ^ k) / Real.sin (x / 2 ^ k) / 2 ^ k with hcdef
  have hterm : ∀ k : ℕ, Real.tan (x / 2 ^ (k + 1)) / 2 ^ (k + 1) = c (k + 1) - c k := by
    intro k
    have e := ram_tan_eq (x / 2 ^ (k + 1)) (hs (k + 1)) (hc (k + 1) (by omega))
    have h2 : 2 * (x / 2 ^ (k + 1)) = x / 2 ^ k := by
      rw [pow_succ]; field_simp
    rw [h2] at e
    simp only [hcdef]
    rw [e]
    rw [pow_succ]
    field_simp
  have hsum : Summable (fun k : ℕ => Real.tan (x / 2 ^ (k + 1)) / 2 ^ (k + 1)) := by
    refine Summable.of_norm_bounded_eventually_nat summable_geometric_two ?_
    have h1 : Tendsto (fun n : ℕ => x / 2 ^ (n + 1)) atTop (𝓝 0) :=
      ht0.comp (tendsto_add_atTop_nat 1)
    have h2 := h1.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [h2] with k hk
    apply ram_norm_le
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (k + 1))]
    simpa using hk
  rw [hsum.hasSum_iff_tendsto_nat]
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, Real.tan (x / 2 ^ (i + 1)) / 2 ^ (i + 1)
      = c n - Real.cos x / Real.sin x := by
    intro n
    simp_rw [hterm]
    rw [Finset.sum_range_sub (fun k => c k) n]
    simp [hcdef]
  simp_rw [hpart]
  apply Tendsto.sub_const
  have hlim : Tendsto (fun n : ℕ => Real.cos (x / 2 ^ n) / (Real.sinc (x / 2 ^ n) * x))
      atTop (𝓝 (1 / x)) := by
    have key : Tendsto (fun n : ℕ => Real.cos (x / 2 ^ n) / (Real.sinc (x / 2 ^ n) * x))
        atTop (𝓝 (Real.cos 0 / (Real.sinc 0 * x))) :=
      ((Real.continuous_cos.tendsto 0).comp ht0).div
        (((Real.continuous_sinc.tendsto 0).comp ht0).mul_const x) (by simp [hx0])
    simpa using key
  refine hlim.congr (fun n => ?_)
  have ht : x / 2 ^ n ≠ 0 := by positivity
  simp only [hcdef]
  rw [Real.sinc_of_ne_zero ht]
  have := hs n
  field_simp
