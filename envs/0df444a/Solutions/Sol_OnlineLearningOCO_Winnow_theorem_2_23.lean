-- Prove2me | solution 1 for OnlineLearningOCO.Winnow.theorem_2_23
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:09:03.951015+00:00
-- url     : https://prove2.me/submissions/b1c6af35-06da-4adc-9d79-97bec652b1a7

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_uegWeights
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

theorem OLW_uegw_zero {d : ℕ} (η lam : ℝ) (z : ℕ → Fin d → ℝ) (i : Fin d) :
    uegWeights η lam z 0 i = lam := by simp [uegWeights]

theorem OLW_uegw_succ {d : ℕ} (η lam : ℝ) (z : ℕ → Fin d → ℝ) (t : ℕ) (i : Fin d) :
    uegWeights η lam z (t + 1) i = uegWeights η lam z t i * Real.exp (-η * z t i) := by
  simp only [uegWeights, sum_range_succ, mul_add, Real.exp_add]; ring

theorem OLW_ulog {d : ℕ} (hd : 0 < d) (u : ℝ) (hu : 0 ≤ u) :
    u * Real.log (u / (Real.exp 1 * (1 / (d : ℝ)))) = (Real.log d - 1) * u + u * Real.log u := by
  rcases hu.eq_or_lt with h | h
  · subst h; simp
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [Real.log_div h.ne' (by positivity), Real.log_mul (Real.exp_pos 1).ne' (by positivity),
      Real.log_exp, one_div, Real.log_inv]
    ring

theorem solution {d : ℕ} (η lam : ℝ) (hη : 0 < η) (hlam : 0 < lam) (z : ℕ → Fin d → ℝ)
    (hz : ∀ t i, -1 ≤ η * z t i) (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) (T : ℕ) :
    (∑ t ∈ range T, ∑ i, (uegWeights η lam z t i - u i) * z t i ≤
      ((d : ℝ) * lam + ∑ i, u i * Real.log (u i / (Real.exp 1 * lam))) / η +
        η * ∑ t ∈ range T, ∑ i, uegWeights η lam z t i * z t i ^ 2) ∧
    (0 < d →
      ∑ t ∈ range T, ∑ i, (uegWeights η (1 / (d : ℝ)) z t i - u i) * z t i ≤
        (1 + (Real.log d - 1) * ∑ i, u i + ∑ i, u i * Real.log (u i)) / η +
          η * ∑ t ∈ range T, ∑ i, uegWeights η (1 / (d : ℝ)) z t i * z t i ^ 2) := by
  refine ⟨OLW_sum η lam hη hlam z hz (uegWeights η lam z) (OLW_uegw_zero η lam z)
    (OLW_uegw_succ η lam z) u hu T, ?_⟩
  intro hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h := OLW_sum η (1 / (d : ℝ)) hη (by positivity) z hz (uegWeights η (1 / (d : ℝ)) z)
    (OLW_uegw_zero η _ z) (OLW_uegw_succ η _ z) u hu T
  have e : ∑ i, u i * Real.log (u i / (Real.exp 1 * (1 / (d : ℝ)))) =
      (Real.log d - 1) * ∑ i, u i + ∑ i, u i * Real.log (u i) := by
    rw [sum_congr rfl (fun i _ => OLW_ulog hd (u i) (hu i)), sum_add_distrib, mul_sum]
  rw [e, mul_one_div_cancel hd'.ne'] at h
  refine h.trans (le_of_eq ?_)
  ring
