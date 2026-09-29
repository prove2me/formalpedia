-- Prove2me | solution 1 for ProxNewton.Exact.search_direction_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:13:15.225336+00:00
-- url     : https://prove2.me/submissions/fd105436-6b54-4cf0-b48c-c9538711dfea

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Variational inequality satisfied by a search direction. -/
theorem aux_sdp_vi {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ d : EuclideanSpace ℝ (Fin n))
    (hD : Convex ℝ D) (hh : ConvexOn ℝ D h)
    (hsym : (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric)
    (hSD : IsSearchDirection g D h x H Δ) (hd : x + d ∈ D) :
    0 ≤ ⟪gradient g x + H Δ, d - Δ⟫ + h (x + d) - h (x + Δ) := by
  set G := gradient g x
  set w := d - Δ with hw
  set A := ⟪G + H Δ, w⟫ + h (x + d) - h (x + Δ) with hA
  set B := ⟪H w, w⟫ with hB
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t / 2 * B := by
    intro t ht0 ht1
    have heq : x + (Δ + t • w) = (1 - t) • (x + Δ) + t • (x + d) := by
      rw [hw]; module
    have hmem : x + (Δ + t • w) ∈ D := by
      rw [heq]
      exact hD hSD.1 hd (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    have hmin := hSD.2 _ hmem
    have hconv := hh.2 hSD.1 hd (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    rw [← heq, smul_eq_mul, smul_eq_mul] at hconv
    have e1 : ⟪G, Δ + t • w⟫ = ⟪G, Δ⟫ + t * ⟪G, w⟫ := by
      rw [inner_add_right, real_inner_smul_right]
    have hs : ⟪H w, Δ⟫ = ⟪H Δ, w⟫ := by
      have := hsym w Δ
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, real_inner_comm]
    have e2 : ⟪H (Δ + t • w), Δ + t • w⟫ = ⟪H Δ, Δ⟫ + 2 * t * ⟪H Δ, w⟫ + t ^ 2 * B := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hs, hB]
      ring
    have e3 : ⟪G + H Δ, w⟫ = ⟪G, w⟫ + ⟪H Δ, w⟫ := inner_add_left _ _ _
    rw [e1, e2] at hmin
    have hprod : 0 ≤ t * (A + t / 2 * B) := by
      rw [hA, e3]
      nlinarith
    exact (mul_nonneg_iff_of_pos_left ht0).mp hprod
  by_contra hneg
  push Not at hneg
  have hB1 : 0 < |B| + 1 := by positivity
  set t := min 1 (-A / (|B| + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hB1)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -A / (|B| + 1) := min_le_right _ _
  have h3 : t * (|B| + 1) ≤ -A := by rwa [le_div_iff₀ hB1] at ht2
  have h4 : t / 2 * B ≤ t / 2 * (|B| + 1) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith [le_abs_self B]
  have := key t ht0 ht1
  nlinarith

/-- Operator norm bound for a symmetric operator with `mI ⪯ H ⪯ MI`, `m > 0`. -/
theorem aux_sdp_norm_le {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) (hH : IsBoundedBetween H m M)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖H v‖ ≤ M * ‖v‖ := by
  obtain ⟨hsym, hb⟩ := hH
  have hsym' : ∀ a b, ⟪H a, b⟫ = ⟪a, H b⟫ := fun a b => by simpa using hsym a b
  have hpsd : ∀ a, 0 ≤ ⟪H a, a⟫ := fun a => le_trans (by positivity) (hb a).1
  have cs : ∀ a b, ⟪H a, b⟫ ^ 2 ≤ ⟪H a, a⟫ * ⟪H b, b⟫ := by
    intro a b
    have hq : ∀ t : ℝ, 0 ≤ ⟪H b, b⟫ * (t * t) + 2 * ⟪H a, b⟫ * t + ⟪H a, a⟫ := by
      intro t
      have := hpsd (a + t • b)
      have hba : ⟪H b, a⟫ = ⟪H a, b⟫ := by rw [hsym' b a, real_inner_comm]
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hba] at this
      nlinarith
    have := discrim_le_zero hq
    simp only [discrim] at this
    nlinarith
  have h1 := cs v (H v)
  have hvv : ⟪H v, H v⟫ = ‖H v‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [hvv] at h1
  have h2 : ⟪H v, v⟫ * ⟪H (H v), H v⟫ ≤ (M * ‖v‖ ^ 2) * (M * ‖H v‖ ^ 2) :=
    mul_le_mul (hb v).2 (hb (H v)).2 (hpsd _) (by positivity)
  have h3 : (‖H v‖ ^ 2) ^ 2 ≤ (M * ‖v‖) ^ 2 * ‖H v‖ ^ 2 := by nlinarith
  rcases eq_or_lt_of_le (norm_nonneg (H v)) with h0 | hpos
  · rw [← h0]; positivity
  · have h4 : ‖H v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by
      have hp2 : 0 < ‖H v‖ ^ 2 := by positivity
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

end ProxNewton.Exact

open ProxNewton.Exact

theorem solution (m M m2 M2 : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hm2 : 0 < m2) (hmM2 : m2 ≤ M2) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) (D : Set (EuclideanSpace ℝ (Fin n)))
        (h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
        (H1 H2 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (Δ1 Δ2 : EuclideanSpace ℝ (Fin n)),
        IsProperClosedConvex D h →
        IsBoundedBetween H1 m M → IsBoundedBetween H2 m2 M2 →
        IsSearchDirection g D h x H1 Δ1 → IsSearchDirection g D h x H2 Δ2 →
        ‖Δ1 - Δ2‖ ≤
          Real.sqrt ((1 + θ) / m) * Real.sqrt ‖(H2 - H1) Δ1‖ * Real.sqrt ‖Δ1‖ := by
  have hMM : 0 < M + M2 := by linarith
  have hθpos : 0 < m * (M + M2) / m2 ^ 2 := by positivity
  refine ⟨m * (M + M2) / m2 ^ 2, hθpos, ?_⟩
  intro n g D h x H1 H2 Δ1 Δ2 hh hB1 hB2 hS1 hS2
  obtain ⟨_, hD, hconv, _⟩ := hh
  have vi1 := aux_sdp_vi g D h x H1 Δ1 Δ2 hD hconv hB1.1 hS1 hS2.1
  have vi2 := aux_sdp_vi g D h x H2 Δ2 Δ1 hD hconv hB2.1 hS2 hS1.1
  set θ := m * (M + M2) / m2 ^ 2 with hθ
  have hkey : ⟪H2 (Δ1 - Δ2), Δ1 - Δ2⟫ ≤ ⟪(H2 - H1) Δ1, Δ1 - Δ2⟫ := by
    have : ⟪gradient g x + H1 Δ1, Δ2 - Δ1⟫ + ⟪gradient g x + H2 Δ2, Δ1 - Δ2⟫ =
        ⟪(H2 - H1) Δ1, Δ1 - Δ2⟫ - ⟪H2 (Δ1 - Δ2), Δ1 - Δ2⟫ := by
      simp only [ContinuousLinearMap.sub_apply, map_sub, inner_add_left, inner_sub_left,
        inner_sub_right]
      ring
    linarith
  have hlow : m2 * ‖Δ1 - Δ2‖ ^ 2 ≤ ⟪H2 (Δ1 - Δ2), Δ1 - Δ2⟫ := (hB2.2 _).1
  have hcs : ⟪(H2 - H1) Δ1, Δ1 - Δ2⟫ ≤ ‖(H2 - H1) Δ1‖ * ‖Δ1 - Δ2‖ := real_inner_le_norm _ _
  have he : ‖Δ1 - Δ2‖ ≤ ‖(H2 - H1) Δ1‖ / m2 := by
    rcases eq_or_lt_of_le (norm_nonneg (Δ1 - Δ2)) with h0 | hpos
    · rw [← h0]; positivity
    · rw [le_div_iff₀ hm2]; nlinarith
  have hKn : ‖(H2 - H1) Δ1‖ ≤ (M + M2) * ‖Δ1‖ := by
    have a1 := aux_sdp_norm_le H1 m M hm (by linarith) hB1 Δ1
    have a2 := aux_sdp_norm_le H2 m2 M2 hm2 (by linarith) hB2 Δ1
    calc ‖(H2 - H1) Δ1‖ = ‖H2 Δ1 - H1 Δ1‖ := by simp
      _ ≤ ‖H2 Δ1‖ + ‖H1 Δ1‖ := norm_sub_le _ _
      _ ≤ (M + M2) * ‖Δ1‖ := by linarith
  have hK0 := norm_nonneg ((H2 - H1) Δ1)
  have hD0 := norm_nonneg Δ1
  have hsq : ‖Δ1 - Δ2‖ ^ 2 ≤ (1 + θ) / m * ‖(H2 - H1) Δ1‖ * ‖Δ1‖ := by
    have h1 : ‖Δ1 - Δ2‖ ^ 2 ≤ (‖(H2 - H1) Δ1‖ / m2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) he 2
    have h2 : (‖(H2 - H1) Δ1‖ / m2) ^ 2 ≤ (M + M2) / m2 ^ 2 * ‖(H2 - H1) Δ1‖ * ‖Δ1‖ := by
      rw [div_pow, mul_assoc, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
    have h3 : (M + M2) / m2 ^ 2 ≤ (1 + θ) / m := by
      have : (1 + θ) / m = 1 / m + (M + M2) / m2 ^ 2 := by
        rw [hθ]; field_simp
      rw [this]
      have : 0 < 1 / m := by positivity
      linarith
    have h4 : (M + M2) / m2 ^ 2 * ‖(H2 - H1) Δ1‖ * ‖Δ1‖ ≤
        (1 + θ) / m * ‖(H2 - H1) Δ1‖ * ‖Δ1‖ := by
      apply mul_le_mul_of_nonneg_right _ hD0
      exact mul_le_mul_of_nonneg_right h3 hK0
    linarith
  have hθ0 : 0 ≤ (1 + θ) / m := div_nonneg (by linarith) hm.le
  rw [← Real.sqrt_mul hθ0, ← Real.sqrt_mul (mul_nonneg hθ0 hK0)]
  exact Real.le_sqrt_of_sq_le hsq
