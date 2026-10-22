-- Prove2me | solution 1 for ProxAlg.FixedPoint.prox_optimality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:12:16.14083+00:00
-- url     : https://prove2.me/submissions/b2a00c42-9a67-473d-a08c-1fd26af641e2

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
    (hf : MoreauProx.Decomposition.GammaZero f)
    (v x : EuclideanSpace ℝ (Fin n)) :
    MoreauProx.Decomposition.IsProx f v x ↔ v - x ∈ subdifferential f x := by
  unfold IsProx proxObjective subdifferential
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hprox
    obtain ⟨x0, hx0⟩ := hf.exists_ne_top
    have hxtop : f x ≠ ⊤ := by
      intro h
      have h1 := hprox x0
      rw [h, EReal.coe_add_top] at h1
      rcases pa_cases (f x0) (hf.ne_bot x0) with h2 | ⟨c, h2⟩
      · exact hx0 h2
      · rw [h2, ← EReal.coe_add] at h1
        exact EReal.coe_ne_top _ (top_le_iff.1 h1)
    rcases pa_cases (f x) (hf.ne_bot x) with h | ⟨a, ha⟩
    · exact absurd h hxtop
    refine ⟨lt_top_iff_ne_top.2 hxtop, fun z => ?_⟩
    rcases pa_cases (f z) (hf.ne_bot z) with hz | ⟨b, hb⟩
    · rw [hz]; exact le_top
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
        0 ≤ (⟪x - v, z - x⟫_ℝ + b - a) + t * (‖z - x‖ ^ 2 / 2) := by
      intro t ht0 ht1
      have hconv := pa_convex f hf x z a b ha hb t ht0.le ht1
      have h1 := hprox ((1 - t) • x + t • z)
      have h2 : (((‖(1 - t) • x + t • z - v‖ ^ 2 / 2 : ℝ)) : EReal) + f ((1 - t) • x + t • z) ≤
          (((‖(1 - t) • x + t • z - v‖ ^ 2 / 2 : ℝ)) : EReal) + (((1 - t) * a + t * b : ℝ) : EReal) :=
        add_le_add le_rfl hconv
      have h3 := h1.trans h2
      rw [ha, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
      have hu : (1 - t) • x + t • z - v = (x - v) + t • (z - x) := by module
      rw [hu, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at h3
      have : 0 ≤ t * ((⟪x - v, z - x⟫_ℝ + b - a) + t * (‖z - x‖ ^ 2 / 2)) := by nlinarith [h3]
      exact (mul_nonneg_iff_of_pos_left ht0).1 this
    have h5 := pa_aux _ _ (by positivity) key
    have e2 : ⟪v - x, z - x⟫_ℝ = -⟪x - v, z - x⟫_ℝ := by rw [← inner_neg_left, neg_sub]
    linarith
  · rintro ⟨hxtop, hsub⟩ u
    rcases pa_cases (f x) (hf.ne_bot x) with h | ⟨a, ha⟩
    · rw [h] at hxtop; exact absurd hxtop (lt_irrefl _)
    rcases pa_cases (f u) (hf.ne_bot u) with hu | ⟨b, hb⟩
    · rw [hu, EReal.coe_add_top]; exact le_top
    have h := hsub u
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have e1 : u - v = (u - x) + (x - v) := by abel
    rw [e1, norm_add_sq_real]
    have e2 : ⟪v - x, u - x⟫_ℝ = -⟪u - x, x - v⟫_ℝ := by
      rw [← inner_neg_right, neg_sub, real_inner_comm]
    nlinarith [sq_nonneg ‖u - x‖]
