-- Prove2me | solution 1 for YieldPostpone.Interplay.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:06:33.280904+00:00
-- url     : https://prove2.me/submissions/46e2cde6-1bb6-48f7-ac40-2bbe0fd7dfea

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting
set_option autoImplicit false
open YieldPostpone.Interplay

theorem ll_ra {a b x p : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hxa : x < a / 2) (hp : 0 < p) :
    p * min (a - b * p) x ≤ ((a - x) / b) * x ∧
      (p * min (a - b * p) x = ((a - x) / b) * x → p = (a - x) / b) := by
  have hps : b * ((a - x) / b) = a - x := by field_simp
  have hpos : 0 < (a - x) / b := div_pos (by linarith) hb
  rcases le_or_gt p ((a - x) / b) with h | h
  · have hmin : a - b * p ≥ x := by nlinarith
    rw [min_eq_right hmin]
    refine ⟨by nlinarith, fun e => ?_⟩
    have : p * x = ((a - x) / b) * x := e
    exact mul_right_cancel₀ hx.ne' this
  · have hmin : a - b * p < x := by nlinarith
    rw [min_eq_left hmin.le]
    have key : p * (a - b * p) < ((a - x) / b) * x := by
      have h1 : a - b * (((a - x) / b) + p) < 0 := by nlinarith
      nlinarith
    exact ⟨key.le, fun e => absurd e key.ne⟩

theorem ll_rb {a b x p : ℝ} (ha : 0 < a) (hb : 0 < b) (hxa : a / 2 ≤ x) :
    p * min (a - b * p) x ≤ (a / (2 * b)) * (a / 2) ∧
      (0 < p → p * min (a - b * p) x = (a / (2 * b)) * (a / 2) → p = a / (2 * b)) := by
  have e : (a / (2 * b)) * (a / 2) = a ^ 2 / (4 * b) := by field_simp; ring
  rw [e]
  have h4 : 4 * b * (p * (a - b * p)) ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 2 * b * p)]
  have hle : a ^ 2 / (4 * b) ≥ p * (a - b * p) := by
    rw [ge_iff_le, le_div_iff₀ (by positivity)]; linarith
  refine ⟨?_, fun hp e2 => ?_⟩
  · rcases le_or_gt p 0 with hp | hp
    · have : min (a - b * p) x ≥ 0 ∨ True := Or.inr trivial
      have hm : 0 ≤ min (a - b * p) x := le_min (by nlinarith) (by linarith)
      have : p * min (a - b * p) x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hm
      have : 0 ≤ a ^ 2 / (4 * b) := by positivity
      linarith
    · calc p * min (a - b * p) x ≤ p * (a - b * p) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hp.le
        _ ≤ _ := hle
  · have h5 : p * (a - b * p) ≥ a ^ 2 / (4 * b) := by
      calc a ^ 2 / (4 * b) = p * min (a - b * p) x := e2.symm
        _ ≤ p * (a - b * p) := mul_le_mul_of_nonneg_left (min_le_left _ _) hp.le
    have h6 : a ^ 2 ≤ 4 * b * (p * (a - b * p)) := by
      rw [ge_iff_le, div_le_iff₀ (by positivity)] at h5; linarith
    have h7 : (a - 2 * b * p) ^ 2 ≤ 0 := by nlinarith
    have h8 : a - 2 * b * p = 0 := by nlinarith [sq_nonneg (a - 2 * b * p)]
    field_simp
    linarith

theorem ll_ra_val {a b x : ℝ} (hb : 0 < b) :
    ((a - x) / b) * min (a - b * ((a - x) / b)) x = ((a - x) / b) * x := by
  have hps : b * ((a - x) / b) = a - x := by field_simp
  rw [hps]; simp

theorem ll_rb_val {a b x : ℝ} (hb : 0 < b) (hxa : a / 2 ≤ x) :
    (a / (2 * b)) * min (a - b * (a / (2 * b))) x = (a / (2 * b)) * (a / 2) := by
  have : b * (a / (2 * b)) = a / 2 := by field_simp
  rw [this]
  have : a - a / 2 = a / 2 := by ring
  rw [this, min_eq_left hxa]

theorem solution (P : Params) (hP : P.Valid) (x : ℝ) :
    (0 < x → x < P.a / 2 →
      ∀ p : ℝ, pAdm P p →
        ((∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x) ↔ p = (P.a - x) / P.b)) ∧
    (P.a / 2 ≤ x →
      ∀ p : ℝ, pAdm P p →
        ((∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x) ↔ p = P.a / (2 * P.b))) := by
  obtain ⟨ha, hb, -, -, -, -⟩ := hP
  have hsr : ∀ q y : ℝ, salesRev P q y = q * min (P.a - P.b * q) y := fun q y => rfl
  constructor
  · intro hx hxa p hp
    have hps : pAdm P ((P.a - x) / P.b) := by
      refine ⟨div_pos (by linarith) hb, ?_⟩
      exact div_lt_div_of_pos_right (by linarith) hb
    constructor
    · intro hmax
      have h1 := hmax _ hps
      rw [hsr, hsr, ll_ra_val hb] at h1
      have h2 := (ll_ra ha hb hx hxa hp.1)
      exact h2.2 (le_antisymm h2.1 h1)
    · rintro rfl
      intro p' hp'
      rw [hsr, hsr, ll_ra_val hb]
      exact (ll_ra ha hb hx hxa hp'.1).1
  · intro hxa' p hp
    have hps : pAdm P (P.a / (2 * P.b)) := by
      refine ⟨by positivity, ?_⟩
      exact (div_lt_div_iff₀ (by positivity) hb).2 (by nlinarith)
    constructor
    · intro hmax
      have h1 := hmax _ hps
      rw [hsr, hsr, ll_rb_val hb hxa'] at h1
      have h2 := (ll_rb (p := p) (x := x) ha hb hxa')
      exact h2.2 hp.1 (le_antisymm h2.1 h1)
    · rintro rfl
      intro p' hp'
      rw [hsr, hsr, ll_rb_val hb hxa']
      exact (ll_rb ha hb hxa').1
