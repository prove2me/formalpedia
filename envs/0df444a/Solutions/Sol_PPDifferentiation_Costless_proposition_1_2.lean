-- Prove2me | solution 2 for PPDifferentiation.Costless.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:01:24.119995+00:00
-- url     : https://prove2.me/submissions/8f05a970-75cc-4893-a5f0-c436e4180611

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting
import Theorems.Thm_PPDifferentiation_Costless_lemma_1_dominance

-- carved verbatim out of submission 01f99999-e7fc-4d06-9506-7dec27496e32, lines 678-725

section
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

lemma ppd_profPP_zero_left (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA ≤ xB)
    (h : xA + xB ≤ 0) : profPP t xA xB = 0 := by
  unfold profPP
  have : ∀ x ∈ Set.uIcc (0:ℝ) 1, max 0 (adv t xA xB x) = 0 := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    apply max_eq_left
    rw [ppd_adv_eq]
    have : 0 ≤ t * (xB - xA) := mul_nonneg ht.le (by linarith)
    nlinarith [hx.1, hx.2]
  rw [intervalIntegral.integral_congr this]; simp

lemma ppd_profPP_zero_right (t : ℝ) (ht : 0 < t) (xi xj : ℝ) (hij : xj ≤ xi)
    (h : 2 ≤ xi + xj) : profPP t xi xj = 0 := by
  unfold profPP
  have : ∀ x ∈ Set.uIcc (0:ℝ) 1, max 0 (adv t xi xj x) = 0 := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    apply max_eq_left
    rw [ppd_adv_eq]
    have : 0 ≤ t * (xi - xj) := mul_nonneg ht.le (by linarith)
    nlinarith [hx.1, hx.2]
  rw [intervalIntegral.integral_congr this]; simp

lemma ppd_profPP_self (t a : ℝ) : profPP t a a = 0 := by
  unfold profPP
  have : ∀ x ∈ Set.uIcc (0:ℝ) 1, max 0 (adv t a a x) = 0 := by
    intro x _
    rw [ppd_adv_eq]; simp
  rw [intervalIntegral.integral_congr this]; simp

lemma ppd_profPP_reflect (t xi xj : ℝ) : profPP t (1 - xi) (1 - xj) = profPP t xi xj := by
  unfold profPP
  have e : ∀ x, adv t (1 - xi) (1 - xj) x = adv t xi xj (1 - x) := by
    intro x; unfold adv; ring
  simp_rw [e]
  have := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1)
    (fun x => max 0 (adv t xi xj x)) 1
  simpa using this

lemma ppd_exists_pos (t : ℝ) (ht : 0 < t) (b : ℝ) : ∃ x, 0 < profPP t x b := by
  rcases lt_trichotomy b (1 / 2) with h | h | h
  · refine ⟨1 - b, ?_⟩
    rw [ppd_profPP_right t ht b (1 - b) (by linarith) (by linarith) (by linarith)]
    nlinarith
  · refine ⟨0, ?_⟩
    rw [ppd_profPP_left t ht 0 b (by linarith) (by linarith) (by linarith)]
    rw [h]; nlinarith
  · refine ⟨1 - b, ?_⟩
    rw [ppd_profPP_left t ht (1 - b) b (by linarith) (by linarith) (by linarith)]
    nlinarith

lemma ppd_FOC (t : ℝ) (ht : 0 < t) (a b : ℝ) (hab : a < b) (h0 : 0 < a + b) (h2 : a + b < 2)
    (hmax : ∀ x, profPP t x b ≤ profPP t a b) : b = 3 * a := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ, P = fun x => t * ((b - x) * (x + b) ^ 2) / 4 := ⟨_, rfl⟩
  have hloc : ∀ x, -b < x → x < b → x < 2 - b → profPP t x b = P x := by
    intro x h1 h2' h3
    rw [ppd_profPP_left t ht x b h2'.le (by linarith) (by linarith), hP]
    ring
  have ha1 : -b < a := by linarith
  have ha2 : a < min b (2 - b) := lt_min hab (by linarith)
  have hlm : IsLocalMax P a := by
    have hn := Ioo_mem_nhds ha1 ha2
    filter_upwards [hn] with x hx
    have h := hmax x
    rw [hloc x hx.1 (lt_of_lt_of_le hx.2 (min_le_left _ _)) (lt_of_lt_of_le hx.2 (min_le_right _ _)),
      hloc a ha1 hab (by linarith)] at h
    exact h
  have h1 : HasDerivAt (fun x : ℝ => b - x) (-1) a := by
    simpa using (hasDerivAt_id a).const_sub b
  have h2' : HasDerivAt (fun x : ℝ => (x + b) ^ 2) (2 * (a + b)) a := by
    exact (((hasDerivAt_id a).add_const b).pow 2).congr_deriv (by simp)
  have h3 := ((h1.mul h2').const_mul t).div_const 4
  have hd : HasDerivAt P (t * (-1 * (a + b) ^ 2 + (b - a) * (2 * (a + b))) / 4) a := by
    rw [hP]; exact h3
  have h0' := hlm.hasDerivAt_eq_zero hd
  have h4 : t * ((a + b) * (b - 3 * a)) = 0 := by linear_combination 4 * h0'
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h ht.ne'
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h h0.ne'
    · linarith

lemma ppd_bound34 (t : ℝ) (ht : 0 < t) (x : ℝ) : profPP t x (3 / 4) ≤ t / 8 := by
  rcases le_or_gt x (-3 / 4) with h1 | h1
  · rw [ppd_profPP_zero_left t ht x (3 / 4) (by linarith) (by linarith)]; linarith
  rcases le_or_gt x (3 / 4) with h2 | h2
  · rw [ppd_profPP_left t ht x (3 / 4) h2 (by linarith) (by linarith)]
    have := mul_nonneg ht.le (mul_nonneg (sq_nonneg (x - 1 / 4)) (by linarith : (0:ℝ) ≤ x + 5 / 4))
    nlinarith
  rcases le_or_gt x (5 / 4) with h3 | h3
  · rw [ppd_profPP_right t ht (3 / 4) x h2.le (by linarith) (by linarith)]
    have h5 : (x - 3 / 4) * (2 - 3 / 4 - x) ^ 2 ≤ 1 / 2 := by nlinarith [sq_nonneg (2 - 3 / 4 - x)]
    nlinarith
  · rw [ppd_profPP_zero_right t ht x (3 / 4) (by linarith) (by linarith)]; linarith

theorem solution (t : ℝ) (ht : 0 < t) :
    IsPosEqPP t (1/4) (3/4) ∧
    (∀ a b : ℝ, a ≤ b → IsPosEqPP t a b → a = 1/4 ∧ b = 3/4) ∧
    PPStrictlyDominant t (1/4) (3/4) ∧
    profPP t (1/4) (3/4) = t / 8 ∧ profPP t (3/4) (1/4) = t / 8 := by
  have V1 : profPP t (1/4) (3/4) = t / 8 := by
    rw [ppd_profPP_left t ht (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num)]; ring
  have V2 : profPP t (3/4) (1/4) = t / 8 := by
    rw [ppd_profPP_right t ht (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num)]; ring
  refine ⟨⟨fun x => ?_, fun x => ?_⟩, ?_, ?_, V1, V2⟩
  · rw [V1]; exact ppd_bound34 t ht x
  · rw [V2]
    have := ppd_profPP_reflect t (1 - x) (1 / 4)
    have e : profPP t x (1 / 4) = profPP t (1 - x) (3 / 4) := by
      have := ppd_profPP_reflect t x (1 / 4)
      rw [← this]; norm_num
    rw [e]; exact ppd_bound34 t ht _
  · intro a b hab ⟨hA, hB⟩
    obtain ⟨xa, hxa⟩ := ppd_exists_pos t ht b
    obtain ⟨xb, hxb⟩ := ppd_exists_pos t ht a
    have pA : 0 < profPP t a b := lt_of_lt_of_le hxa (hA xa)
    have pB : 0 < profPP t b a := lt_of_lt_of_le hxb (hB xb)
    have hne : a < b := by
      rcases hab.lt_or_eq with h | h
      · exact h
      · subst h; rw [ppd_profPP_self] at pA; exact absurd pA (lt_irrefl _)
    have h0 : 0 < a + b := by
      by_contra hc
      push_neg at hc
      rw [ppd_profPP_zero_left t ht a b hne.le hc] at pA
      exact absurd pA (lt_irrefl _)
    have h2 : a + b < 2 := by
      by_contra hc
      push_neg at hc
      rw [ppd_profPP_zero_right t ht b a hne.le (by linarith)] at pB
      exact absurd pB (lt_irrefl _)
    have f1 := ppd_FOC t ht a b hne h0 h2 hA
    have f2 := ppd_FOC t ht (1 - b) (1 - a) (by linarith) (by linarith) (by linarith) (by
      intro x
      have e1 : profPP t x (1 - a) = profPP t (1 - x) a := by
        have := ppd_profPP_reflect t (1 - x) a
        rw [← this]; simp
      rw [e1, ppd_profPP_reflect t b a]
      exact hB (1 - x))
    constructor <;> linarith
  · obtain ⟨hd, _, _⟩ := PPDifferentiation.Costless.lemma_1_dominance t ht (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num)
    exact hd

end
