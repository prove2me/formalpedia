-- Prove2me | solution 1 for ProxNewton.Exact.search_direction_properties
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:55:44.263991+00:00
-- url     : https://prove2.me/submissions/4a2b7454-ebb5-4fe2-8efd-0bdc57f1f2e4

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

/-- Descent-type upper bound for a `C¹` function with `L1`-Lipschitz gradient
(with the non-sharp constant `L1 ‖Δ‖²`). -/
theorem aux_sdp_descent {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 < t) :
    g (x + t • Δ) ≤ g x + t * ⟪gradient g x, Δ⟫ + L1 * ‖Δ‖ ^ 2 * t ^ 2 := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hder : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => g (x + s • Δ)) ⟪gradient g (x + s • Δ), Δ⟫ s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • Δ) Δ s := by
      simpa using ((hasDerivAt_id s).smul_const Δ).const_add x
    have h2 := (hdiff (x + s • Δ)).hasFDerivAt.comp_hasDerivAt s h1
    have he : (fderiv ℝ g (x + s • Δ)) Δ = ⟪gradient g (x + s • Δ), Δ⟫ := by
      simp [gradient, InnerProductSpace.toDual_symm_apply]
    rw [he] at h2
    exact h2
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => g (x + s • Δ))
    (fun s => ⟪gradient g (x + s • Δ), Δ⟫) ht
    (fun s _ => (hder s).continuousAt.continuousWithinAt) (fun s _ => hder s)
  simp only [zero_smul, add_zero, sub_zero] at hcd
  have key : g (x + t • Δ) - g x = t * ⟪gradient g (x + c • Δ), Δ⟫ := by
    rw [hcd]; field_simp
  have h3 : ⟪gradient g (x + c • Δ), Δ⟫ - ⟪gradient g x, Δ⟫ ≤ L1 * ‖Δ‖ ^ 2 * t := by
    rw [← inner_sub_left]
    calc ⟪gradient g (x + c • Δ) - gradient g x, Δ⟫
        ≤ ‖gradient g (x + c • Δ) - gradient g x‖ * ‖Δ‖ := real_inner_le_norm _ _
      _ ≤ (L1 * ‖(x + c • Δ) - x‖) * ‖Δ‖ := by gcongr; exact hgL _ _
      _ = L1 * c * ‖Δ‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc.1.le]; ring
      _ ≤ L1 * ‖Δ‖ ^ 2 * t := by
          nlinarith [hc.2, mul_nonneg hL1 (sq_nonneg ‖Δ‖)]
  nlinarith

theorem aux_sdp_eq {n : ℕ} (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    x + t • Δ = (1 - t) • x + t • (x + Δ) := by
  rw [sub_smul, one_smul, smul_add]; abel

end ProxNewton.Exact

open ProxNewton.Exact

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsPosDef H) (hΔ : IsSearchDirection g D h x H Δ) :
    (∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      compositeObj g D h (x + t • Δ) ≤
        ((g x + h x + t * predDecrease g h x Δ + C * t ^ 2 : ℝ) : EReal)) ∧
    predDecrease g h x Δ ≤ -⟪H Δ, Δ⟫ := by
  obtain ⟨_, hDc, hhc, _⟩ := hD
  obtain ⟨hxΔ, hmin⟩ := hΔ
  have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → x + t • Δ ∈ D := by
    intro t ht0 ht1
    rw [aux_sdp_eq]
    exact hDc hx hxΔ (by linarith) ht0 (by ring)
  have hconv : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      h (x + t • Δ) ≤ (1 - t) * h x + t * h (x + Δ) := by
    intro t ht0 ht1
    have := hhc.2 hx hxΔ (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
    rw [aux_sdp_eq]
    simpa [smul_eq_mul] using this
  refine ⟨⟨L1 * ‖Δ‖ ^ 2, fun t ht0 ht1 => ?_⟩, ?_⟩
  · have hm := hmem t ht0.le ht1
    simp only [compositeObj, hm, if_true]
    rw [EReal.coe_le_coe_iff]
    have h1 := aux_sdp_descent g L1 hg hL1 hgL x Δ t ht0
    have h2 := hconv t ht0.le ht1
    unfold predDecrease
    nlinarith
  · have key : ∀ t : ℝ, 0 < t → t < 1 →
        predDecrease g h x Δ + 1 / 2 * (1 + t) * ⟪H Δ, Δ⟫ ≤ 0 := by
      intro t ht0 ht1
      have h1 := hmin (t • Δ) (hmem t ht0.le ht1.le)
      have h2 := hconv t ht0.le ht1.le
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
      have h3 : (1 - t) * (predDecrease g h x Δ + 1 / 2 * (1 + t) * ⟪H Δ, Δ⟫) ≤ 0 := by
        unfold predDecrease
        nlinarith
      by_contra hc
      push Not at hc
      have := mul_pos (by linarith : (0 : ℝ) < 1 - t) hc
      linarith
    have hlim : Tendsto (fun t : ℝ => predDecrease g h x Δ + 1 / 2 * (1 + t) * ⟪H Δ, Δ⟫)
        (𝓝[<] 1) (𝓝 (predDecrease g h x Δ + 1 / 2 * (1 + 1) * ⟪H Δ, Δ⟫)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact ((continuous_const.add ((continuous_const.mul
        (continuous_const.add continuous_id)).mul continuous_const)).tendsto 1)
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ),
        predDecrease g h x Δ + 1 / 2 * (1 + t) * ⟪H Δ, Δ⟫ ≤ 0 := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact key t ht.1 ht.2
    have := le_of_tendsto hlim hev
    linarith
