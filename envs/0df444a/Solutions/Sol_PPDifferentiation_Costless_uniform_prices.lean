-- Prove2me | solution 1 for PPDifferentiation.Costless.uniform_prices
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:54:21.087887+00:00
-- url     : https://prove2.me/submissions/40e46260-f574-4d68-b6af-e5e71f3fe3d8

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting

set_option autoImplicit false
open MeasureTheory PPDifferentiation.Costless

lemma ppd_ramp_dec (k m : ℝ) (hk : 0 ≤ k) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    ∫ x in (0:ℝ)..1, max 0 (k * (m - x)) = k * m ^ 2 / 2 := by
  have hc : Continuous fun x : ℝ => max 0 (k * (m - x)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := m)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (0:ℝ)..m, max 0 (k * (m - x)) = ∫ x in (0:ℝ)..m, k * (m - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    simp only
    exact max_eq_right (mul_nonneg hk (by linarith [hx.2]))
  have e2 : ∫ x in m..1, max 0 (k * (m - x)) = ∫ x in m..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h1] at hx
    simp only
    exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hk (by linarith [hx.1]))
  rw [e1, e2]
  have : ∫ x in (0:ℝ)..m, k * (m - x) = k * m ^ 2 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => k * (m * x - x ^ 2 / 2))
      (f' := fun x => k * (m - x))]
    · ring
    · intro x _
      have := (((hasDerivAt_id x).const_mul m).sub ((hasDerivAt_pow 2 x).div_const 2)).const_mul k
      exact this.congr_deriv (by simp)
    · exact (by fun_prop : Continuous fun x : ℝ => k * (m - x)).intervalIntegrable _ _
  rw [this]; simp

lemma ppd_ramp_inc (k m : ℝ) (hk : 0 ≤ k) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    ∫ x in (0:ℝ)..1, max 0 (k * (x - m)) = k * (1 - m) ^ 2 / 2 := by
  have hc : Continuous fun x : ℝ => max 0 (k * (x - m)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := m)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (0:ℝ)..m, max 0 (k * (x - m)) = ∫ x in (0:ℝ)..m, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    simp only
    exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hk (by linarith [hx.2]))
  have e2 : ∫ x in m..1, max 0 (k * (x - m)) = ∫ x in m..1, k * (x - m) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h1] at hx
    simp only
    exact max_eq_right (mul_nonneg hk (by linarith [hx.1]))
  rw [e1, e2]
  have : ∫ x in m..1, k * (x - m) = k * (1 - m) ^ 2 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => k * (x ^ 2 / 2 - m * x))
      (f' := fun x => k * (x - m))]
    · ring
    · intro x _
      have := (((hasDerivAt_pow 2 x).div_const 2).sub ((hasDerivAt_id x).const_mul m)).const_mul k
      exact this.congr_deriv (by simp)
    · exact (by fun_prop : Continuous fun x : ℝ => k * (x - m)).intervalIntegrable _ _
  rw [this]; simp

lemma ppd_adv_eq (t xi xj x : ℝ) : adv t xi xj x = t * (xi - xj) * (2 * x - xi - xj) := by
  unfold adv; ring

lemma ppd_profPP_left (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA ≤ xB)
    (h0 : 0 ≤ xA + xB) (h2 : xA + xB ≤ 2) :
    profPP t xA xB = t * (xB - xA) * (xA + xB)^2 / 4 := by
  have e : ∀ x, adv t xA xB x = (2 * t * (xB - xA)) * ((xA + xB) / 2 - x) := by
    intro x; rw [ppd_adv_eq]; ring
  unfold profPP
  simp_rw [e]
  rw [ppd_ramp_dec _ _ (by nlinarith) (by linarith) (by linarith)]
  ring

lemma ppd_profPP_right (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA ≤ xB)
    (h0 : 0 ≤ xA + xB) (h2 : xA + xB ≤ 2) :
    profPP t xB xA = t * (xB - xA) * (2 - xA - xB)^2 / 4 := by
  have e : ∀ x, adv t xB xA x = (2 * t * (xB - xA)) * (x - (xA + xB) / 2) := by
    intro x; rw [ppd_adv_eq]; ring
  unfold profPP
  simp_rw [e]
  rw [ppd_ramp_inc _ _ (by nlinarith) (by linarith) (by linarith)]
  ring

/-- clamp to `[0,1]` -/
noncomputable def ppdCl (c : ℝ) : ℝ := max 0 (min 1 c)

lemma ppdCl_nonneg (c : ℝ) : 0 ≤ ppdCl c := le_max_left _ _

lemma ppdCl_le_one (c : ℝ) : ppdCl c ≤ 1 := by
  unfold ppdCl; exact max_le zero_le_one (min_le_left _ _)

lemma ppdCl_of_mem (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) : ppdCl c = c := by
  unfold ppdCl; rw [min_eq_right h1, max_eq_right h0]

lemma ppdCl_of_le0 (c : ℝ) (h : c ≤ 0) : ppdCl c = 0 := by
  unfold ppdCl; exact max_eq_left ((min_le_right _ _).trans h)

lemma ppdCl_of_ge1 (c : ℝ) (h : 1 ≤ c) : ppdCl c = 1 := by
  unfold ppdCl; rw [min_eq_left h]; exact max_eq_right zero_le_one

lemma ppdCl_le_c (c : ℝ) (h : 0 < c) : ppdCl c ≤ c := by
  unfold ppdCl; exact max_le h.le (min_le_right _ _)

lemma ppdCl_pos (c : ℝ) (h : 0 < ppdCl c) : 0 < c := by
  by_contra hc
  push_neg at hc
  have := ppdCl_of_le0 c hc
  linarith

lemma ppdCl_lt_one (c : ℝ) (h : ppdCl c < 1) : c < 1 := by
  by_contra hc
  push_neg at hc
  have := ppdCl_of_ge1 c hc
  linarith

lemma ppdCl_one_sub (c : ℝ) : ppdCl (1 - c) = 1 - ppdCl c := by
  rcases le_total c 0 with h | h
  · rw [ppdCl_of_le0 c h, ppdCl_of_ge1 (1 - c) (by linarith)]; norm_num
  · rcases le_total c 1 with h' | h'
    · rw [ppdCl_of_mem c h h', ppdCl_of_mem (1 - c) (by linarith) (by linarith)]
    · rw [ppdCl_of_ge1 c h', ppdCl_of_le0 (1 - c) (by linarith)]; norm_num

lemma ppd_vol_Iio (c : ℝ) : (volume (Set.Iio c ∩ Set.Icc (0:ℝ) 1)).toReal = ppdCl c := by
  rcases le_or_gt c 0 with h | h
  · have : Set.Iio c ∩ Set.Icc (0:ℝ) 1 = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, h2, _⟩; linarith
    rw [this, ppdCl_of_le0 c h]; simp
  · rcases le_or_gt c 1 with h' | h'
    · have : Set.Iio c ∩ Set.Icc (0:ℝ) 1 = Set.Ico 0 c := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
      rw [this, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith), ppdCl_of_mem c h.le h']
      ring
    · have : Set.Iio c ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 1 := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc]
        constructor
        · rintro ⟨_, h2⟩; exact h2
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, h2⟩
      rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num), ppdCl_of_ge1 c h'.le]
      ring

lemma ppd_vol_Ioi (c : ℝ) : (volume (Set.Ioi c ∩ Set.Icc (0:ℝ) 1)).toReal = ppdCl (1 - c) := by
  rcases lt_or_ge c 0 with h | h
  · have : Set.Ioi c ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 1 := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, h2⟩
    rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num), ppdCl_of_ge1 (1 - c) (by linarith)]
    ring
  · rcases lt_or_ge c 1 with h' | h'
    · have : Set.Ioi c ∩ Set.Icc (0:ℝ) 1 = Set.Ioc c 1 := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
        constructor
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
      rw [this, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
        ppdCl_of_mem (1 - c) (by linarith) (by linarith)]
    · have : Set.Ioi c ∩ Set.Icc (0:ℝ) 1 = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨h1, _, h3⟩; linarith
      rw [this, ppdCl_of_le0 (1 - c) (by linarith)]; simp

lemma ppd_set_dec (k m p : ℝ) (hk : 0 < k) : {x : ℝ | p < k * (m - x)} = Set.Iio (m - p / k) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Iio]
  have : p / k < m - x ↔ p < (m - x) * k := div_lt_iff₀ hk
  constructor
  · intro h
    have h2 : p / k < m - x := this.2 (by linarith [mul_comm k (m - x)])
    linarith
  · intro h
    have h2 := this.1 (by linarith : p / k < m - x)
    linarith [mul_comm k (m - x)]

lemma ppd_set_inc (k m p : ℝ) (hk : 0 < k) : {x : ℝ | p < k * (x - m)} = Set.Ioi (m + p / k) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioi]
  have : p / k < x - m ↔ p < (x - m) * k := div_lt_iff₀ hk
  constructor
  · intro h
    have h2 : p / k < x - m := this.2 (by linarith [mul_comm k (x - m)])
    linarith
  · intro h
    have h2 := this.1 (by linarith : p / k < x - m)
    linarith [mul_comm k (x - m)]

lemma ppd_tie_null (k : ℝ) (hk : k ≠ 0) (f : ℝ → ℝ) (hf : ∀ x y, f x = f y → x = y) (d : ℝ) :
    volume ({x : ℝ | d = k * f x} ∩ Set.Icc (0:ℝ) 1) = 0 := by
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  have h1 : d = k * f x := hx.1
  have h2 : d = k * f y := hy.1
  exact hf x y (mul_left_cancel₀ hk (h1.symm.trans h2))

lemma ppd_adv_left (t xi xj k m : ℝ) (hk : k = 2 * t * (xj - xi)) (hm : m = (xi + xj) / 2) (x : ℝ) :
    adv t xi xj x = k * (m - x) := by
  rw [ppd_adv_eq, hk, hm]; ring

lemma ppd_adv_right (t xi xj k m : ℝ) (hk : k = 2 * t * (xi - xj)) (hm : m = (xi + xj) / 2) (x : ℝ) :
    adv t xi xj x = k * (x - m) := by
  rw [ppd_adv_eq, hk, hm]; ring

lemma ppd_leadShare_left (t xi xj p k m : ℝ) (ht : 0 < t) (h : xi < xj)
    (hk : k = 2 * t * (xj - xi)) (hm : m = (xi + xj) / 2) :
    leadShare t xi xj p = ppdCl (m - p / k) := by
  have hk0 : 0 < k := by rw [hk]; nlinarith
  unfold leadShare
  simp only [ppd_adv_left t xi xj k m hk hm]
  rw [ppd_set_dec k m p hk0, ppd_vol_Iio]

lemma ppd_leadShare_right (t xi xj p k m : ℝ) (ht : 0 < t) (h : xj < xi)
    (hk : k = 2 * t * (xi - xj)) (hm : m = (xi + xj) / 2) :
    leadShare t xi xj p = ppdCl ((1 - m) - p / k) := by
  have hk0 : 0 < k := by rw [hk]; nlinarith
  unfold leadShare
  simp only [ppd_adv_right t xi xj k m hk hm]
  rw [ppd_set_inc k m p hk0, ppd_vol_Ioi]
  congr 1; ring

lemma ppd_uShare_left (t xi xj pi pj k m : ℝ) (ht : 0 < t) (h : xi < xj)
    (hk : k = 2 * t * (xj - xi)) (hm : m = (xi + xj) / 2) :
    uShare t xi xj pi pj = ppdCl ((m + pj / k) - pi / k) := by
  have hk0 : 0 < k := by rw [hk]; nlinarith
  unfold uShare
  simp only [ppd_adv_left t xi xj k m hk hm]
  have e : {x : ℝ | pi - pj = k * (m - x)} ∩ Set.Icc (0:ℝ) 1 ⊆ {x : ℝ | pi - pj = k * (m - x)} :=
    Set.inter_subset_left
  rw [ppd_tie_null k hk0.ne' (fun x => m - x) (fun x y hxy => by simpa using hxy), ppd_set_dec k m _ hk0,
    ppd_vol_Iio]
  simp only [ENNReal.toReal_zero, zero_div, add_zero]
  congr 1; ring

lemma ppd_uShare_right (t xi xj pi pj k m : ℝ) (ht : 0 < t) (h : xj < xi)
    (hk : k = 2 * t * (xi - xj)) (hm : m = (xi + xj) / 2) :
    uShare t xi xj pi pj = ppdCl (((1 - m) + pj / k) - pi / k) := by
  have hk0 : 0 < k := by rw [hk]; nlinarith
  unfold uShare
  simp only [ppd_adv_right t xi xj k m hk hm]
  rw [ppd_tie_null k hk0.ne' (fun x => x - m) (fun x y hxy => by simpa using hxy), ppd_set_inc k m _ hk0,
    ppd_vol_Ioi]
  simp only [ENNReal.toReal_zero, zero_div, add_zero]
  congr 1; ring

lemma ppd_leadProf_left (t xi xj p k m : ℝ) (ht : 0 < t) (h : xi < xj)
    (hk : k = 2 * t * (xj - xi)) (hm : m = (xi + xj) / 2) :
    leadProf t xi xj p = p * ppdCl (m - p / k) := by
  unfold leadProf; rw [ppd_leadShare_left t xi xj p k m ht h hk hm]

lemma ppd_leadProf_right (t xi xj p k m : ℝ) (ht : 0 < t) (h : xj < xi)
    (hk : k = 2 * t * (xi - xj)) (hm : m = (xi + xj) / 2) :
    leadProf t xi xj p = p * ppdCl ((1 - m) - p / k) := by
  unfold leadProf; rw [ppd_leadShare_right t xi xj p k m ht h hk hm]

lemma ppd_uProf_left (t xi xj pi pj k m : ℝ) (ht : 0 < t) (h : xi < xj)
    (hk : k = 2 * t * (xj - xi)) (hm : m = (xi + xj) / 2) :
    uProf t xi xj pi pj = pi * ppdCl ((m + pj / k) - pi / k) := by
  unfold uProf; rw [ppd_uShare_left t xi xj pi pj k m ht h hk hm]

lemma ppd_uProf_right (t xi xj pi pj k m : ℝ) (ht : 0 < t) (h : xj < xi)
    (hk : k = 2 * t * (xi - xj)) (hm : m = (xi + xj) / 2) :
    uProf t xi xj pi pj = pi * ppdCl (((1 - m) + pj / k) - pi / k) := by
  unfold uProf; rw [ppd_uShare_right t xi xj pi pj k m ht h hk hm]

/-- price bound -/
lemma ppd_G1 (k M : ℝ) (hk : 0 < k) (q : ℝ) : q * ppdCl (M - q / k) ≤ k * M ^ 2 / 4 := by
  obtain ⟨u, rfl⟩ : ∃ u, q = k * u := ⟨q / k, by field_simp⟩
  rw [mul_div_cancel_left₀ _ hk.ne']
  have hM : 0 ≤ k * M ^ 2 / 4 := by positivity
  rcases le_or_gt u 0 with h | h
  · have : k * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le h
    nlinarith [ppdCl_nonneg (M - u)]
  · have hku : 0 < k * u := mul_pos hk h
    rcases le_or_gt (M - u) 0 with h2 | h2
    · rw [ppdCl_of_le0 _ h2]; linarith
    · have := ppdCl_le_c _ h2
      have h3 : k * u * ppdCl (M - u) ≤ k * u * (M - u) := mul_le_mul_of_nonneg_left this hku.le
      nlinarith [mul_nonneg hk.le (sq_nonneg (M / 2 - u))]

lemma ppd_G1_attain (k M : ℝ) (hk : 0 < k) (h0 : 0 ≤ M) (h2 : M ≤ 2) :
    (k * M / 2) * ppdCl (M - (k * M / 2) / k) = k * M ^ 2 / 4 := by
  have : M - (k * M / 2) / k = M / 2 := by field_simp; ring
  rw [this, ppdCl_of_mem _ (by linarith) (by linarith)]; ring

lemma ppd_G2 (k M q : ℝ) (hk : 0 < k) (hM : M ≠ 0) (h : k * M ^ 2 / 4 ≤ q * ppdCl (M - q / k)) :
    q = k * M / 2 := by
  obtain ⟨u, rfl⟩ : ∃ u, q = k * u := ⟨q / k, by field_simp⟩
  rw [mul_div_cancel_left₀ _ hk.ne'] at h
  have hM2 : 0 < k * M ^ 2 / 4 := by positivity
  have hku : 0 < k * u := by
    by_contra hc
    push_neg at hc
    nlinarith [ppdCl_nonneg (M - u)]
  have hu : 0 < u := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hcl : 0 < ppdCl (M - u) := by
    by_contra hc
    push_neg at hc
    nlinarith [ppdCl_nonneg (M - u)]
  have h2 := ppdCl_le_c _ (ppdCl_pos _ hcl)
  have h3 : k * u * ppdCl (M - u) ≤ k * u * (M - u) := mul_le_mul_of_nonneg_left h2 hku.le
  have h4 : k * (M / 2 - u) ^ 2 ≤ 0 := by nlinarith
  have h5 : (M / 2 - u) ^ 2 ≤ 0 := by
    by_contra hc; push_neg at hc; nlinarith [mul_pos hk hc]
  have h6 : M / 2 - u = 0 := by nlinarith [sq_nonneg (M / 2 - u)]
  have : u = M / 2 := by linarith
  rw [this]; ring

theorem solution (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA < xB)
    (hlo : -2 < xA + xB) (hhi : xA + xB < 4) :
    IsPriceNE t xA xB (t * (xB - xA) * (2 + xA + xB) / 3) (t * (xB - xA) * (4 - xA - xB) / 3) ∧
    uProf t xA xB (t * (xB - xA) * (2 + xA + xB) / 3) (t * (xB - xA) * (4 - xA - xB) / 3) =
      t * (xB - xA) * (2 + xA + xB)^2 / 18 ∧
    uProf t xB xA (t * (xB - xA) * (4 - xA - xB) / 3) (t * (xB - xA) * (2 + xA + xB) / 3) =
      t * (xB - xA) * (4 - xA - xB)^2 / 18 := by
  have hd : 0 < xB - xA := by linarith
  have hk0 : 0 < 2 * t * (xB - xA) := by positivity
  set k : ℝ := 2 * t * (xB - xA) with hk
  set m : ℝ := (xA + xB) / 2 with hm
  have hk' : k = 2 * t * (xB - xA) := hk
  have hm' : m = (xA + xB) / 2 := hm
  have hm2 : m = (xB + xA) / 2 := by rw [hm']; ring
  set pA : ℝ := t * (xB - xA) * (2 + xA + xB) / 3 with hpA
  set pB : ℝ := t * (xB - xA) * (4 - xA - xB) / 3 with hpB
  have eA : ∀ q r, uProf t xA xB q r = q * ppdCl ((m + r / k) - q / k) := fun q r =>
    ppd_uProf_left t xA xB q r k m ht hAB hk' hm'
  have eB : ∀ q r, uProf t xB xA q r = q * ppdCl (((1 - m) + r / k) - q / k) := fun q r =>
    ppd_uProf_right t xB xA q r k m ht hAB hk' hm2
  have MA : m + pB / k = (xA + xB + 2) / 3 := by
    rw [hpB, hm', hk']; field_simp; ring
  have MB : (1 - m) + pA / k = (4 - xA - xB) / 3 := by
    rw [hpA, hm', hk']; field_simp; ring
  have pA' : pA = k * ((xA + xB + 2) / 3) / 2 := by rw [hpA, hk']; ring
  have pB' : pB = k * ((4 - xA - xB) / 3) / 2 := by rw [hpB, hk']; ring
  have vA : uProf t xA xB pA pB = k * ((xA + xB + 2) / 3) ^ 2 / 4 := by
    rw [eA, MA, pA']
    exact ppd_G1_attain k _ hk0 (by linarith) (by linarith)
  have vB : uProf t xB xA pB pA = k * ((4 - xA - xB) / 3) ^ 2 / 4 := by
    rw [eB, MB, pB']
    exact ppd_G1_attain k _ hk0 (by linarith) (by linarith)
  refine ⟨⟨fun q => ?_, fun q => ?_⟩, ?_, ?_⟩
  · rw [vA, eA q, MA]; exact ppd_G1 k _ hk0 q
  · rw [vB, eB q, MB]; exact ppd_G1 k _ hk0 q
  · rw [vA, hk']; ring
  · rw [vB, hk']; ring
