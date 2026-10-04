-- Prove2me | solution 1 for ShorNonsmooth.SubgradMethod.constant_step_finite_termination_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:45:02.07671+00:00
-- url     : https://prove2.me/submissions/6c4019fc-cfa8-48f7-a088-6bb67954fbdb

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace P63b7a17c

open ShorNonsmooth.SubgradMethod

lemma step_bound {n : ℕ} (x gx c : EuclideanSpace ℝ (Fin n)) (r h : ℝ) (hh : 0 < h)
    (hne : gx ≠ 0) (hin : r * ‖gx‖ ≤ inner ℝ gx (x - c)) :
    ‖(x - (h / ‖gx‖) • gx) - c‖ ^ 2 ≤ ‖x - c‖ ^ 2 - h * (2 * r - h) := by
  have hg : 0 < ‖gx‖ := norm_pos_iff.mpr hne
  have e : (x - (h / ‖gx‖) • gx) - c = (x - c) - (h / ‖gx‖) • gx := by abel
  have hc : inner ℝ (x - c) gx = inner ℝ gx (x - c) := real_inner_comm _ _
  rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, hc]
  have ha : ‖h / ‖gx‖‖ = h / ‖gx‖ := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hh hg)]
  rw [ha]
  have h1 : h / ‖gx‖ * ‖gx‖ = h := by field_simp
  have h2 : h / ‖gx‖ * (r * ‖gx‖) ≤ h / ‖gx‖ * inner ℝ gx (x - c) :=
    mul_le_mul_of_nonneg_left hin (div_pos hh hg).le
  have h3 : h / ‖gx‖ * (r * ‖gx‖) = r * h := by
    rw [show h / ‖gx‖ * (r * ‖gx‖) = r * (h / ‖gx‖ * ‖gx‖) by ring, h1]
  rw [h1]
  nlinarith

lemma ne_zero_of_not_min {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x gx : EuclideanSpace ℝ (Fin n)) (hg : ShorNonsmooth.AlmostDiff.IsSubgradient f x gx)
    (hx : x ∉ MinSet f) : gx ≠ 0 := by
  intro h0
  apply hx
  intro y
  have := hg y
  rw [h0, inner_zero_left] at this
  linarith

lemma inner_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (c : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall c r ⊆ MinSet f)
    (x gx : EuclideanSpace ℝ (Fin n)) (hg : ShorNonsmooth.AlmostDiff.IsSubgradient f x gx)
    (hne : gx ≠ 0) : r * ‖gx‖ ≤ inner ℝ gx (x - c) := by
  have hgp : 0 < ‖gx‖ := norm_pos_iff.mpr hne
  set y : EuclideanSpace ℝ (Fin n) := c + (r / ‖gx‖) • gx with hy
  have hyb : y ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall, dist_eq_norm, hy, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos hr hgp)]
    rw [div_mul_cancel₀ _ hgp.ne']
  have hym : f y ≤ f x := hball hyb x
  have hs := hg y
  have e : y - x = (r / ‖gx‖) • gx - (x - c) := by rw [hy]; abel
  rw [e, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hs
  have h4 : r / ‖gx‖ * ‖gx‖ ^ 2 = r * ‖gx‖ := by field_simp
  rw [h4] at hs
  linarith

end P63b7a17c

open Filter Topology in
open ShorNonsmooth.SubgradMethod in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (c : EuclideanSpace ℝ (Fin n)) (r h : ℝ)
    (hh : 0 < h / 2) (hr : h / 2 < r) (hball : Metric.closedBall c r ⊆ MinSet f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ kstar : ℕ, normalizedIter g (fun _ => h) x₀ kstar ∈ MinSet f := by
  have hhp : 0 < h := by linarith
  have hrp : 0 < r := by linarith
  set δ : ℝ := h * (2 * r - h) with hδ
  have hδp : 0 < δ := mul_pos hhp (by linarith)
  by_contra hcon
  push_neg at hcon
  have hd : ∀ k : ℕ, ‖normalizedIter g (fun _ => h) x₀ k - c‖ ^ 2 ≤
      ‖x₀ - c‖ ^ 2 - (k : ℝ) * δ := by
    intro k
    induction k with
    | zero => simp [normalizedIter]
    | succ k ih =>
      have hne := P63b7a17c.ne_zero_of_not_min f _ _ (hg _) (hcon k)
      have hin := P63b7a17c.inner_bound f c r hrp hball _ _ (hg _) hne
      have hs := P63b7a17c.step_bound _ _ c r h hhp hne hin
      have heq : normalizedIter g (fun _ => h) x₀ (k + 1) =
          normalizedIter g (fun _ => h) x₀ k -
            (h / ‖g (normalizedIter g (fun _ => h) x₀ k)‖) •
              g (normalizedIter g (fun _ => h) x₀ k) := by
        rw [normalizedIter, if_neg hne]
      rw [heq]
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (‖x₀ - c‖ ^ 2 / δ)
  have h1 := hd k
  have h2 : 0 ≤ ‖normalizedIter g (fun _ => h) x₀ k - c‖ ^ 2 := sq_nonneg _
  rw [div_lt_iff₀ hδp] at hk
  linarith
