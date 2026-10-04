-- Prove2me | solution 1 for ShorNonsmooth.SubgradMethod.constant_step_level_set_near_minimum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:00:14.023051+00:00
-- url     : https://prove2.me/submissions/d63927cd-a65d-4b38-ae54-d0b8c4853b40

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace Pa73cb9f1

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

/-- If `f` is continuous, `f xs < L` and `f` never takes the value `L` on the open ball
`B(xs, r)`, then `f < L` on that ball (intermediate value theorem on the convex ball). -/
lemma lt_on_ball {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hcont : Continuous f)
    (xs : EuclideanSpace ℝ (Fin n)) (r L : ℝ) (hlt : f xs < L)
    (hne : ∀ w, ‖w - xs‖ < r → f w ≠ L) (z : EuclideanSpace ℝ (Fin n))
    (hz : ‖z - xs‖ < r) : f z < L := by
  by_contra hcon
  push_neg at hcon
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hz
  have hs : IsPreconnected (Metric.ball xs r) := (convex_ball xs r).isPreconnected
  have hxs : xs ∈ Metric.ball xs r := Metric.mem_ball_self hr
  have hzs : z ∈ Metric.ball xs r := by rwa [Metric.mem_ball, dist_eq_norm]
  have hiv := hs.intermediate_value hxs hzs hcont.continuousOn
  obtain ⟨w, hw, hwL⟩ := hiv ⟨hlt.le, hcon⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw
  exact hne w hw hwL

lemma inner_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (xs : EuclideanSpace ℝ (Fin n))
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (x gx : EuclideanSpace ℝ (Fin n)) (hg : ShorNonsmooth.AlmostDiff.IsSubgradient f x gx)
    (hne : gx ≠ 0) (hball : ∀ z, ‖z - xs‖ < R → f z < f x) :
    ρ * ‖gx‖ ≤ inner ℝ gx (x - xs) := by
  have hgp : 0 < ‖gx‖ := norm_pos_iff.mpr hne
  set y : EuclideanSpace ℝ (Fin n) := xs + (ρ / ‖gx‖) • gx with hy
  have hyb : ‖y - xs‖ < R := by
    rw [hy, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ hgp),
      div_mul_cancel₀ _ hgp.ne']
    exact hρR
  have hym : f y < f x := hball y hyb
  have hs := hg y
  have e : y - x = (ρ / ‖gx‖) • gx - (x - xs) := by rw [hy]; abel
  rw [e, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hs
  have h4 : ρ / ‖gx‖ * ‖gx‖ ^ 2 = ρ * ‖gx‖ := by field_simp
  rw [h4] at hs
  linarith

end Pa73cb9f1

open Filter Topology in
open ShorNonsmooth.SubgradMethod in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hM : (MinSet f).Nonempty)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (h : ℝ) (hh : 0 < h) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∀ ε > 0, ∀ xstar ∈ MinSet f, ∃ kstar : ℕ, ∃ xbar : EuclideanSpace ℝ (Fin n),
      f xbar = f (normalizedIter g (fun _ => h) x₀ kstar) ∧
        ‖xbar - xstar‖ < h * (1 + ε) / 2 := by
  intro ε hε xstar hxs
  by_contra H
  push_neg at H
  have hcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hεh : 0 < h * ε := mul_pos hh hε
  have hcon : ∀ k, normalizedIter g (fun _ => h) x₀ k ∉ MinSet f := by
    intro k hk
    have := H k xstar (le_antisymm (hxs _) (hk _))
    rw [sub_self, norm_zero] at this
    nlinarith
  set ρ : ℝ := h * (1 + ε / 2) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; nlinarith
  have hρR : ρ < h * (1 + ε) / 2 := by rw [hρdef]; nlinarith
  set δ : ℝ := h * (2 * ρ - h) with hδ
  have hδp : 0 < δ := by
    rw [hδ, hρdef]; nlinarith
  have hd : ∀ k : ℕ, ‖normalizedIter g (fun _ => h) x₀ k - xstar‖ ^ 2 ≤
      ‖x₀ - xstar‖ ^ 2 - (k : ℝ) * δ := by
    intro k
    induction k with
    | zero => simp [normalizedIter]
    | succ k ih =>
      have hne := Pa73cb9f1.ne_zero_of_not_min f _ _ (hg _) (hcon k)
      have hlt : f xstar < f (normalizedIter g (fun _ => h) x₀ k) := by
        have hk := hcon k
        simp only [MinSet, Set.mem_setOf_eq, not_forall, not_le] at hk
        obtain ⟨y, hy⟩ := hk
        exact lt_of_le_of_lt (hxs y) hy
      have hball : ∀ z, ‖z - xstar‖ < h * (1 + ε) / 2 →
          f z < f (normalizedIter g (fun _ => h) x₀ k) := by
        apply Pa73cb9f1.lt_on_ball f hcont xstar _ _ hlt
        intro w hw heq
        have := H k w heq
        linarith
      have hin := Pa73cb9f1.inner_bound f xstar ρ _ hρ hρR _ _ (hg _) hne hball
      have hs := Pa73cb9f1.step_bound _ _ xstar ρ h hh hne hin
      have heq : normalizedIter g (fun _ => h) x₀ (k + 1) =
          normalizedIter g (fun _ => h) x₀ k -
            (h / ‖g (normalizedIter g (fun _ => h) x₀ k)‖) •
              g (normalizedIter g (fun _ => h) x₀ k) := by
        rw [normalizedIter, if_neg hne]
      rw [heq]
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (‖x₀ - xstar‖ ^ 2 / δ)
  have h1 := hd k
  have h2 : 0 ≤ ‖normalizedIter g (fun _ => h) x₀ k - xstar‖ ^ 2 := sq_nonneg _
  rw [div_lt_iff₀ hδp] at hk
  linarith
