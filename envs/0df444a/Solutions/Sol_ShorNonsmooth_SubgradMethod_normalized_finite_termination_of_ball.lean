-- Prove2me | solution 1 for ShorNonsmooth.SubgradMethod.normalized_finite_termination_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:10:34.192705+00:00
-- url     : https://prove2.me/submissions/1f056654-4f25-474b-b77f-7cc6fa4f9146

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace P7ec298c0

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

end P7ec298c0

open Filter Topology ShorNonsmooth.SubgradMethod in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ MinSet f) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h k)
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h k) atTop atTop)
    (hlimsup : ∃ q < 2 * r, ∀ᶠ k in atTop, h k ≤ q)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℕ, normalizedIter g h x₀ k ∈ MinSet f := by
  obtain ⟨q, hq, hev⟩ := hlimsup
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  set a : ℝ := 2 * r - q with ha
  have hap : 0 < a := by rw [ha]; linarith
  by_contra hcon
  push_neg at hcon
  set d : ℕ → ℝ := fun k => ‖normalizedIter g h x₀ k - c‖ ^ 2 with hd
  set S : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, h k with hS
  have step : ∀ k, K ≤ k → d (k + 1) + a * S (k + 2) ≤ d k + a * S (k + 1) := by
    intro k hk
    have hne := P7ec298c0.ne_zero_of_not_min f _ _ (hg _) (hcon k)
    have hin := P7ec298c0.inner_bound f c r hr hball _ _ (hg _) hne
    have hs := P7ec298c0.step_bound _ _ c r (h (k + 1)) (hpos _) hne hin
    have heq : normalizedIter g h x₀ (k + 1) =
        normalizedIter g h x₀ k -
          (h (k + 1) / ‖g (normalizedIter g h x₀ k)‖) •
            g (normalizedIter g h x₀ k) := by
      rw [normalizedIter, if_neg hne]
    have hSs : S (k + 2) = S (k + 1) + h (k + 1) := by
      simp only [hS]; rw [Finset.sum_range_succ]
    have hqk : h (k + 1) ≤ q := hK (k + 1) (by omega)
    have hp := hpos (k + 1)
    have hdk1 : d (k + 1) ≤ d k - h (k + 1) * (2 * r - h (k + 1)) := by
      simp only [hd]; rw [heq]; exact hs
    rw [hSs]
    nlinarith
  have hind : ∀ m, d (K + m) + a * S (K + m + 1) ≤ d K + a * S (K + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := step (K + m) (by omega)
      have e1 : K + (m + 1) = K + m + 1 := by omega
      have e2 : K + m + 1 + 1 = K + m + 2 := by omega
      rw [e1, e2]
      linarith
  have hT := (tendsto_atTop.mp hdiv) ((d K + a * S (K + 1)) / a + 1)
  obtain ⟨N, hN⟩ := (hT.and (eventually_ge_atTop (K + 1))).exists
  obtain ⟨hN1, hN2⟩ := hN
  have hm := hind (N - K - 1)
  have e : K + (N - K - 1) + 1 = N := by omega
  rw [e] at hm
  have hdn : 0 ≤ d (K + (N - K - 1)) := by simp only [hd]; positivity
  have hSN : (d K + a * S (K + 1)) / a + 1 ≤ S N := hN1
  have h3 : (d K + a * S (K + 1)) / a * a = d K + a * S (K + 1) := div_mul_cancel₀ _ hap.ne'
  nlinarith
