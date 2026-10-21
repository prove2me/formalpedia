-- Prove2me | solution 1 for OnlineLearningOCO.Winnow.eq_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:01:11.338973+00:00
-- url     : https://prove2.me/submissions/3c3dd0b6-2fe9-4457-8c55-4061febb14b5

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_Winnow
set_option autoImplicit false
open Finset
open OnlineLearningOCO.Winnow

theorem OLW_exp_le (x : ℝ) (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  by_cases h : |x| ≤ 1
  · have := abs_le.1 (Real.abs_exp_sub_one_sub_id_le h)
    linarith [this.2]
  · have hx1 : x < -1 := by
      rcases lt_abs.1 (not_le.1 h) with h1 | h1 <;> linarith
    have : Real.exp x ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith

theorem OLW_log_ineq (lam u w : ℝ) (hlam : 0 < lam) (hu : 0 ≤ u) (hw : 0 < w) :
    u * Real.log (w / lam) - w ≤ u * Real.log (u / (Real.exp 1 * lam)) := by
  rcases hu.eq_or_lt with h | h
  · subst h; simp; exact hw.le
  · have e1 : Real.log (u / (Real.exp 1 * lam)) = Real.log u - 1 - Real.log lam := by
      rw [Real.log_div h.ne' (by positivity), Real.log_mul (Real.exp_pos 1).ne' hlam.ne',
        Real.log_exp]; ring
    have e2 : Real.log (w / lam) = Real.log w - Real.log lam := Real.log_div hw.ne' hlam.ne'
    have e3 : Real.log (w / u) = Real.log w - Real.log u := Real.log_div hw.ne' h.ne'
    have h4 := Real.log_le_sub_one_of_pos (div_pos hw h)
    rw [e3] at h4
    have h5 : u * (Real.log w - Real.log u) ≤ u * (w / u - 1) := mul_le_mul_of_nonneg_left h4 hu
    have h6 : u * (w / u - 1) = w - u := by field_simp
    rw [e1, e2]
    nlinarith

/-- per-coordinate bound -/
theorem OLW_coord (η lam : ℝ) (hη : 0 < η) (hlam : 0 < lam) (z w : ℕ → ℝ)
    (hz : ∀ t, -1 ≤ η * z t) (hw0 : w 0 = lam) (hws : ∀ t, w (t + 1) = w t * Real.exp (-η * z t))
    (u : ℝ) (hu : 0 ≤ u) (T : ℕ) :
    ∑ t ∈ range T, (w t - u) * z t ≤
      (lam + u * Real.log (u / (Real.exp 1 * lam))) / η + η * ∑ t ∈ range T, w t * z t ^ 2 := by
  have hpos : ∀ t, 0 < w t := by
    intro t
    induction t with
    | zero => rw [hw0]; exact hlam
    | succ t ih => rw [hws]; exact mul_pos ih (Real.exp_pos _)
  have hstep : ∀ t, η * (w t * z t) ≤ w t - w (t + 1) + η ^ 2 * (w t * z t ^ 2) := by
    intro t
    have h := OLW_exp_le (-(η * z t)) (by linarith [hz t])
    rw [hws, show -η * z t = -(η * z t) by ring]
    have := mul_le_mul_of_nonneg_left h (hpos t).le
    nlinarith
  have hsum : η * ∑ t ∈ range T, w t * z t ≤ lam - w T + η ^ 2 * ∑ t ∈ range T, w t * z t ^ 2 := by
    have h1 : ∑ t ∈ range T, η * (w t * z t) ≤
        ∑ t ∈ range T, (w t - w (t + 1) + η ^ 2 * (w t * z t ^ 2)) := sum_le_sum (fun t _ => hstep t)
    rw [sum_add_distrib, sum_range_sub', ← mul_sum, ← mul_sum, hw0] at h1
    exact h1
  have hexp : ∀ n, w n = lam * Real.exp (-η * ∑ t ∈ range n, z t) := by
    intro n
    induction n with
    | zero => simp [hw0]
    | succ n ih =>
      rw [hws, ih, sum_range_succ, mul_add, Real.exp_add]; ring
  have hlog : Real.log (w T / lam) = -η * ∑ t ∈ range T, z t := by
    rw [hexp T, mul_div_cancel_left₀ _ hlam.ne', Real.log_exp]
  have hkey := OLW_log_ineq lam u (w T) hlam hu (hpos T)
  rw [hlog] at hkey
  have hexpand : ∑ t ∈ range T, (w t - u) * z t = ∑ t ∈ range T, w t * z t - u * ∑ t ∈ range T, z t := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl (fun t _ => by ring)
  rw [hexpand]
  set A := ∑ t ∈ range T, w t * z t
  set Z := ∑ t ∈ range T, z t
  set B := ∑ t ∈ range T, w t * z t ^ 2
  set L := Real.log (u / (Real.exp 1 * lam))
  have h1 : η * (A - u * Z) ≤ lam + u * L + η ^ 2 * B := by nlinarith
  have h2 : (lam + u * L) / η + η * B = (lam + u * L + η ^ 2 * B) / η := by field_simp
  rw [h2, le_div_iff₀ hη]
  linarith

theorem OLW_sum {d : ℕ} (η lam : ℝ) (hη : 0 < η) (hlam : 0 < lam) (z : ℕ → Fin d → ℝ)
    (hz : ∀ t i, -1 ≤ η * z t i) (w : ℕ → Fin d → ℝ) (hw0 : ∀ i, w 0 i = lam)
    (hws : ∀ t i, w (t + 1) i = w t i * Real.exp (-η * z t i))
    (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) (T : ℕ) :
    ∑ t ∈ range T, ∑ i, (w t i - u i) * z t i ≤
      ((d : ℝ) * lam + ∑ i, u i * Real.log (u i / (Real.exp 1 * lam))) / η +
        η * ∑ t ∈ range T, ∑ i, w t i * z t i ^ 2 := by
  have hc : ∀ i, ∑ t ∈ range T, (w t i - u i) * z t i ≤
      (lam + u i * Real.log (u i / (Real.exp 1 * lam))) / η + η * ∑ t ∈ range T, w t i * z t i ^ 2 :=
    fun i => OLW_coord η lam hη hlam (fun t => z t i) (fun t => w t i) (fun t => hz t i) (hw0 i)
      (fun t => hws t i) (u i) (hu i) T
  have h1 := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin d))) => hc i)
  rw [sum_comm] at h1
  rw [sum_add_distrib, ← sum_div, sum_add_distrib, ← mul_sum, sum_comm (f := fun i t => w t i * z t i ^ 2)] at h1
  simpa using h1

theorem OLW_34 (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1) (t : ℕ) :
    ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 ≤
      2 * winnowSurrogate d η x y t (winnowWeights d η x y t) := by
  by_cases hm : winnowMargin d η x y t ≤ 0
  · have hm' : y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1) ≤ 0 := hm
    have hz : ∀ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 =
        4 * (winnowWeights d η x y t i * x t i) := by
      intro i
      simp only [winnowZ, hm, if_true]
      rcases hx t i with h | h <;> rcases hy t with h' | h' <;> rw [h, h'] <;> ring
    simp only [winnowSurrogate, hm, if_true]
    rw [sum_congr rfl (fun i _ => hz i), ← mul_sum]
    set p := ∑ i, winnowWeights d η x y t i * x t i
    have hmax : max 0 (1 - y t * (2 * p - 1)) = 1 - y t * (2 * p - 1) := by
      apply max_eq_right
      linarith
    rw [hmax]
    rcases hy t with h' | h' <;> rw [h'] at hm' ⊢ <;> linarith
  · simp [winnowSurrogate, winnowZ, hm]

theorem OLW_33a (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1) (u : Fin d → ℝ) (t : ℕ) :
    winnowSurrogate d η x y t (winnowWeights d η x y t) - winnowSurrogate d η x y t u ≤
      ∑ i, (winnowWeights d η x y t i - u i) * winnowZ d η x y t i := by
  by_cases hm : winnowMargin d η x y t ≤ 0
  · have hm' : y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1) ≤ 0 := hm
    simp only [winnowSurrogate, winnowZ, hm, if_true]
    set p := ∑ i, winnowWeights d η x y t i * x t i
    set q := ∑ i, u i * x t i
    have hmax : max 0 (1 - y t * (2 * p - 1)) = 1 - y t * (2 * p - 1) := by
      apply max_eq_right
      linarith
    have hge : 1 - y t * (2 * q - 1) ≤ max 0 (1 - y t * (2 * q - 1)) := le_max_right _ _
    have hr : ∑ i, (winnowWeights d η x y t i - u i) * (-2 * y t * x t i) = -2 * y t * (p - q) := by
      simp only [p, q, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl (fun i _ => by ring)
    rw [hr, hmax]
    linarith
  · simp [winnowSurrogate, winnowZ, hm]

theorem OLW_surr_nonneg (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (t : ℕ) (v : Fin d → ℝ) :
    0 ≤ winnowSurrogate d η x y t v := by
  unfold winnowSurrogate
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem OLW_33 (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (u : Fin d → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) (hu1 : ∑ i, u i = (k : ℝ)) (T : ℕ) :
    ∑ t ∈ range T, (winnowSurrogate d η x y t (winnowWeights d η x y t) -
        winnowSurrogate d η x y t u) ≤
      ∑ t ∈ range T, ∑ i, (winnowWeights d η x y t i - u i) * winnowZ d η x y t i ∧
    ∑ t ∈ range T, ∑ i, (winnowWeights d η x y t i - u i) * winnowZ d η x y t i ≤
      (k : ℝ) * Real.log d / η +
        η * ∑ t ∈ range T, ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 := by
  refine ⟨sum_le_sum (fun t _ => OLW_33a d η x hx y hy u t), ?_⟩
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      have hk0 : k = 0 := by simpa using hu1.symm
      omega
    · exact h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hz : ∀ t i, -1 ≤ η * winnowZ d η x y t i := by
    intro t i
    simp only [winnowZ]
    split_ifs
    · rcases hx t i with h | h <;> rcases hy t with h' | h' <;> rw [h, h'] <;> nlinarith
    · nlinarith
  have hw0 : ∀ i, winnowWeights d η x y 0 i = 1 / (d : ℝ) := fun i => rfl
  have hws : ∀ t i, winnowWeights d η x y (t + 1) i =
      winnowWeights d η x y t i * Real.exp (-η * winnowZ d η x y t i) := by
    intro t i
    by_cases hm : winnowMargin d η x y t ≤ 0
    · have hm' : y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1) ≤ 0 := hm
      simp only [winnowWeights, winnowZ, hm, hm', if_true]
      congr 2
      ring
    · have hm' : ¬ (y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1) ≤ 0) := hm
      simp [winnowWeights, winnowZ, hm, hm']
  have h := OLW_sum η (1 / (d : ℝ)) hη (by positivity) (winnowZ d η x y) hz
    (winnowWeights d η x y) hw0 hws u (fun i => by rcases hu i with h | h <;> rw [h] <;> norm_num) T
  have e : ∑ i, u i * Real.log (u i / (Real.exp 1 * (1 / (d : ℝ)))) = (Real.log d - 1) * k := by
    rw [← hu1, mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rcases hu i with h | h
    · rw [h]; simp
    · rw [h, Real.log_div one_ne_zero (by positivity), Real.log_mul (Real.exp_pos 1).ne' (by positivity),
        Real.log_exp, one_div, Real.log_inv, Real.log_one]
      ring
  rw [e, mul_one_div_cancel hd'.ne'] at h
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : (1 + (Real.log d - 1) * k) / η ≤ (k : ℝ) * Real.log d / η := by
    apply div_le_div_of_nonneg_right _ hη.le
    nlinarith
  linarith

theorem OLW_310ab (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (u : Fin d → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) (hu1 : ∑ i, u i = (k : ℝ)) (T : ℕ) :
    ((winnowMistakes d η x y T).card : ℝ) ≤
        ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) ∧
    ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) ≤
        (1 / (1 - 2 * η)) *
          (∑ t ∈ range T, winnowSurrogate d η x y t u + (k : ℝ) * Real.log d / η) := by
  constructor
  · unfold winnowMistakes
    rw [card_filter]
    push_cast
    apply sum_le_sum
    intro t _
    by_cases hm : winnowMargin d η x y t ≤ 0
    · have hm' : y t * (2 * ∑ i, winnowWeights d η x y t i * x t i - 1) ≤ 0 := hm
      simp only [hm, if_true, winnowSurrogate]
      refine le_trans ?_ (le_max_right _ _)
      linarith
    · simp only [hm, if_false]
      exact OLW_surr_nonneg d η x y t _
  · obtain ⟨_, h2⟩ := OLW_33 d k hk η hη hη2.le x hx y hy u hu hu1 T
    obtain ⟨h1, _⟩ := OLW_33 d k hk η hη hη2.le x hx y hy u hu hu1 T
    have h34 : ∑ t ∈ range T, ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 ≤
        2 * ∑ t ∈ range T, winnowSurrogate d η x y t (winnowWeights d η x y t) := by
      rw [mul_sum]
      exact sum_le_sum (fun t _ => OLW_34 d η x hx y hy t)
    rw [sum_sub_distrib] at h1
    have hpos : 0 < 1 - 2 * η := by linarith
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left h34 hη.le
    have e : (k : ℝ) * Real.log d / η * 1 = (k : ℝ) * Real.log d / η := mul_one _
    nlinarith

theorem solution (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (u : Fin d → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) (hu1 : ∑ i, u i = (k : ℝ)) (T : ℕ) :
    ∑ t ∈ range T, (winnowSurrogate d η x y t (winnowWeights d η x y t) -
        winnowSurrogate d η x y t u) ≤
      ∑ t ∈ range T, ∑ i, (winnowWeights d η x y t i - u i) * winnowZ d η x y t i ∧
    ∑ t ∈ range T, ∑ i, (winnowWeights d η x y t i - u i) * winnowZ d η x y t i ≤
      (k : ℝ) * Real.log d / η +
        η * ∑ t ∈ range T, ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 :=
  OLW_33 d k hk η hη hη2 x hx y hy u hu hu1 T
