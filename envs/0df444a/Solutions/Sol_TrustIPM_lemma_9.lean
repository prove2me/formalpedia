-- Prove2me | solution 1 for TrustIPM.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:57:53.085433+00:00
-- url     : https://prove2.me/submissions/4d03116c-f96a-4369-a56d-3ec7f8649e49

import Mathlib
import Definitions.Def_TrustIPM_trsModel
open scoped InnerProductSpace RealInnerProductSpace

open TrustIPM in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (g : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ u v, ⟪H u, v⟫_ℝ = ⟪u, H v⟫_ℝ) (r : ℝ) (hr : 0 ≤ r)
    (d : EuclideanSpace ℝ (Fin n)) (hd : d ∈ Metric.closedBall 0 r)
    (hmin : IsMinOn (trsModel (H + (ContinuousLinearMap.adjoint A).comp A) g)
      (Metric.closedBall 0 r) d) :
    ‖A d‖ ≤
      Real.sqrt (-⟪H d, d⟫_ℝ - 2 * trsModel (H + (ContinuousLinearMap.adjoint A).comp A) g d) := by
  set M := H + (ContinuousLinearMap.adjoint A).comp A with hM
  have hq : ∀ t : ℝ, trsModel M g (t • d) = t ^ 2 / 2 * ⟪M d, d⟫_ℝ + t * ⟪g, d⟫_ℝ := by
    intro t
    unfold trsModel
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
    ring
  have hqd : trsModel M g d = 1 / 2 * ⟪M d, d⟫_ℝ + ⟪g, d⟫_ℝ := rfl
  have hMd : ⟪M d, d⟫_ℝ = ⟪H d, d⟫_ℝ + ‖A d‖ ^ 2 := by
    rw [hM, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_left,
      ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have key : ⟪M d, d⟫_ℝ + ⟪g, d⟫_ℝ ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    obtain ⟨a, ha⟩ : ∃ a, a = ⟪M d, d⟫_ℝ := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = ⟪g, d⟫_ℝ := ⟨_, rfl⟩
    rw [← ha, ← hb] at hpos
    obtain ⟨s, hsd⟩ : ∃ s, s = min 1 ((a + b) / (|a| + 1)) := ⟨_, rfl⟩
    have hden : 0 < |a| + 1 := by positivity
    have hs0 : 0 < s := by rw [hsd]; exact lt_min one_pos (div_pos hpos hden)
    have hs1 : s ≤ 1 := by rw [hsd]; exact min_le_left _ _
    have hsa : s * |a| ≤ a + b := by
      have e1 : s ≤ (a + b) / (|a| + 1) := by rw [hsd]; exact min_le_right _ _
      have e2 : 0 ≤ (a + b) / (|a| + 1) := (div_pos hpos hden).le
      calc s * |a| ≤ (a + b) / (|a| + 1) * |a| := mul_le_mul_of_nonneg_right e1 (abs_nonneg a)
        _ ≤ (a + b) / (|a| + 1) * (|a| + 1) := mul_le_mul_of_nonneg_left (by linarith) e2
        _ = a + b := div_mul_cancel₀ _ hden.ne'
    have hmem : (1 - s) • d ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have := mem_closedBall_zero_iff.mp hd
      nlinarith [norm_nonneg d]
    have hle := isMinOn_iff.mp hmin _ hmem
    rw [hq, hqd, ← ha, ← hb] at hle
    have h1 : s * a ≤ s * |a| := mul_le_mul_of_nonneg_left (le_abs_self a) hs0.le
    have h2 : 0 < a + b - s * a / 2 := by linarith
    have h3 := mul_pos hs0 h2
    nlinarith
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [hqd]
  linarith [hMd, key]
