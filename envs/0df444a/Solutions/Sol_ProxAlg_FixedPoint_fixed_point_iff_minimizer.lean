-- Prove2me | solution 1 for ProxAlg.FixedPoint.fixed_point_iff_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:13:35.259385+00:00
-- url     : https://prove2.me/submissions/9a904ad2-8f3f-4388-9e33-4e7c25511282

import Mathlib
import Definitions.Def_ProxAlg_FixedPoint_Basic

set_option autoImplicit false

open scoped InnerProductSpace
open MoreauProx.Decomposition ProxAlg.FixedPoint

lemma pa_cases (e : EReal) (h : e ≠ ⊥) : e = ⊤ ∨ ∃ a : ℝ, e = (a : EReal) := by
  induction e using EReal.rec with
  | bot => exact absurd rfl h
  | top => exact Or.inl rfl
  | coe a => exact Or.inr ⟨a, rfl⟩

lemma pa_aux (c K : ℝ) (hK : 0 ≤ K) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ c + t * K) : 0 ≤ c := by
  by_contra hc
  push_neg at hc
  have hK1 : 0 < 2 * (K + 1) := by linarith
  set t : ℝ := min 1 (-c / (2 * (K + 1))) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hK1)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t * (2 * (K + 1)) ≤ -c := by
    calc t * (2 * (K + 1)) ≤ (-c / (2 * (K + 1))) * (2 * (K + 1)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hK1.le
      _ = -c := by field_simp
  have := h t ht0 ht1
  nlinarith

lemma pa_convex {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : GammaZero f)
    (x z : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (hx : f x = a) (hz : f z = b) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • x + t • z) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have := hf.convex_epigraph (x := (x, a)) (y := (z, b)) (show f x ≤ (a : EReal) by rw [hx])
    (show f z ≤ (b : EReal) by rw [hz]) (sub_nonneg.2 ht1) ht0 (by ring)
  exact this

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : MoreauProx.Decomposition.GammaZero f) (lam : ℝ) (hlam : 0 < lam)
    (xs : EuclideanSpace ℝ (Fin n)) :
    (∀ y, f xs ≤ f y) ↔
      MoreauProx.Decomposition.IsProx (fun u => ((lam : ℝ) : EReal) * f u) xs xs := by
  unfold IsProx proxObjective
  simp only [sub_self, norm_zero]
  constructor
  · intro hmin u
    rcases pa_cases (f u) (hf.ne_bot u) with hu | ⟨b, hb⟩
    · rw [hu, EReal.coe_mul_top_of_pos hlam, EReal.coe_add_top]; exact le_top
    have hle := hmin u
    rw [hb] at hle
    rcases pa_cases (f xs) (hf.ne_bot xs) with hx | ⟨a, ha⟩
    · rw [hx] at hle; exact absurd (top_le_iff.1 hle) (EReal.coe_ne_top _)
    rw [ha] at hle
    have hab : a ≤ b := EReal.coe_le_coe_iff.1 hle
    rw [ha, hb, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    nlinarith [sq_nonneg ‖u - xs‖, mul_le_mul_of_nonneg_left hab hlam.le]
  · intro hprox y
    rcases pa_cases (f y) (hf.ne_bot y) with hy | ⟨b, hb⟩
    · rw [hy]; exact le_top
    rcases pa_cases (f xs) (hf.ne_bot xs) with hx | ⟨a, ha⟩
    · exfalso
      have h := hprox y
      simp only [hx, hb, EReal.coe_mul_top_of_pos hlam] at h
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_add_top] at h
      exact EReal.coe_ne_top _ (top_le_iff.1 h)
    rw [ha, hb, EReal.coe_le_coe_iff]
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ lam * (b - a) + t * (‖y - xs‖ ^ 2 / 2) := by
      intro t ht0 ht1
      have hconv := pa_convex f hf xs y a b ha hb t ht0.le ht1
      rcases pa_cases (f ((1 - t) • xs + t • y)) (hf.ne_bot _) with hw | ⟨w, hw⟩
      · rw [hw] at hconv; exact absurd (top_le_iff.1 hconv) (EReal.coe_ne_top _)
      rw [hw, EReal.coe_le_coe_iff] at hconv
      have h := hprox ((1 - t) • xs + t • y)
      simp only [ha, hw] at h
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at h
      have hu : (1 - t) • xs + t • y - xs = t • (y - xs) := by module
      rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at h
      have : 0 ≤ t * (lam * (b - a) + t * (‖y - xs‖ ^ 2 / 2)) := by
        nlinarith [mul_le_mul_of_nonneg_left hconv hlam.le]
      exact (mul_nonneg_iff_of_pos_left ht0).1 this
    have h5 := pa_aux _ _ (by positivity) key
    nlinarith
