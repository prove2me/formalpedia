-- Prove2me | solution 1 for ShorNonsmooth.SubgradMethod.constant_step_subsequence_near_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:29:58.345818+00:00
-- url     : https://prove2.me/submissions/2acf4df8-3f02-44e4-8211-43e4cd6a1271

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace Pf57b5c8f

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

end Pf57b5c8f

open Filter Topology in
open ShorNonsmooth.SubgradMethod in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hM : (MinSet f).Nonempty) :
    ∀ δ > 0, ∃ hδ > 0, ∀ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) → ∀ x₀ : EuclideanSpace ℝ (Fin n),
        (∃ kstar : ℕ, normalizedIter g (fun _ => hδ) x₀ kstar ∈ MinSet f) ∨
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ i, f (normalizedIter g (fun _ => hδ) x₀ (φ i)) - (⨅ y, f y) < δ := by
  intro δ hδ0
  obtain ⟨xstar, hxs⟩ := hM
  have hcont : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hinf : (⨅ y, f y) = f xstar :=
    le_antisymm (ciInf_le ⟨f xstar, by rintro _ ⟨y, rfl⟩; exact hxs y⟩ xstar) (le_ciInf hxs)
  obtain ⟨η, hη, hηc⟩ := Metric.continuous_iff.mp hcont xstar δ hδ0
  refine ⟨η / 2, by positivity, ?_⟩
  intro g hg x₀
  by_cases hmin : ∃ kstar : ℕ, normalizedIter g (fun _ => η / 2) x₀ kstar ∈ MinSet f
  · exact Or.inl hmin
  right
  push_neg at hmin
  rw [hinf]
  refine Filter.extraction_of_frequently_atTop
    (P := fun k => f (normalizedIter g (fun _ => η / 2) x₀ k) - f xstar < δ) ?_
  rw [Filter.frequently_atTop]
  intro m
  by_contra H
  push_neg at H
  set h : ℝ := η / 2 with hhdef
  have hh : 0 < h := by positivity
  set x : ℕ → EuclideanSpace ℝ (Fin n) := normalizedIter g (fun _ => h) x₀ with hxdef
  have hstep : ∀ k, m ≤ k → ‖x (k + 1) - xstar‖ ^ 2 ≤ ‖x k - xstar‖ ^ 2 - h * η := by
    intro k hk
    have hne := Pf57b5c8f.ne_zero_of_not_min f _ _ (hg (x k)) (hmin k)
    have hball : ∀ z, ‖z - xstar‖ < η → f z < f (x k) := by
      intro z hz
      have h1 := hηc z (by rwa [dist_eq_norm])
      rw [Real.dist_eq] at h1
      have h2 := H k hk
      have h3 := (abs_lt.mp h1).2
      linarith
    have hin := Pf57b5c8f.inner_bound f xstar (3 * η / 4) η (by positivity) (by linarith)
      _ _ (hg (x k)) hne hball
    have hs := Pf57b5c8f.step_bound _ _ xstar (3 * η / 4) h hh hne hin
    have heq : x (k + 1) = x k - (h / ‖g (x k)‖) • g (x k) := by
      rw [hxdef, normalizedIter, if_neg hne]
    rw [heq]
    have : h * (2 * (3 * η / 4) - h) = h * η := by rw [hhdef]; ring
    linarith
  have hd : ∀ j : ℕ, ‖x (m + j) - xstar‖ ^ 2 ≤ ‖x m - xstar‖ ^ 2 - (j : ℝ) * (h * η) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hstep (m + j) (by omega)
      rw [show m + (j + 1) = m + j + 1 by omega]
      push_cast
      linarith
  have hδp : 0 < h * η := by positivity
  obtain ⟨j, hj⟩ := exists_nat_gt (‖x m - xstar‖ ^ 2 / (h * η))
  have h1 := hd j
  have h2 : 0 ≤ ‖x (m + j) - xstar‖ ^ 2 := sq_nonneg _
  rw [div_lt_iff₀ hδp] at hj
  linarith
