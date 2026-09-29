-- Prove2me | solution 1 for ProxNewton.Exact.sufficient_descent_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:03:21.813997+00:00
-- url     : https://prove2.me/submissions/e97bbe91-b767-4658-bbc2-9eb664176b45

import Mathlib
import Definitions.Def_ProxNewton_Exact_Basic

open scoped RealInnerProductSpace Topology
open Filter

namespace ProxNewton.Exact

theorem aux_sds_descent {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (hg : ContDiff ℝ 1 g)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 ≤ t) :
    g (x + t • Δ) ≤ g x + t * ⟪gradient g x, Δ⟫ + L1 / 2 * t ^ 2 * ‖Δ‖ ^ 2 := by
  have hd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hder : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => g (x + s • Δ) - s * ⟪gradient g x, Δ⟫ - L1 / 2 * s ^ 2 * ‖Δ‖ ^ 2)
      (⟪gradient g (x + s • Δ), Δ⟫ - ⟪gradient g x, Δ⟫ - L1 / 2 * (2 * s) * ‖Δ‖ ^ 2) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • Δ) Δ s := by
      simpa using ((hasDerivAt_id s).smul_const Δ).const_add x
    have h2 : HasDerivAt (fun s : ℝ => g (x + s • Δ)) (fderiv ℝ g (x + s • Δ) Δ) s :=
      (hd (x + s • Δ)).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : fderiv ℝ g (x + s • Δ) Δ = ⟪gradient g (x + s • Δ), Δ⟫ := by
      simp [gradient, InnerProductSpace.toDual_symm_apply]
    rw [h3] at h2
    have h4 : HasDerivAt (fun s : ℝ => s * ⟪gradient g x, Δ⟫) ⟪gradient g x, Δ⟫ s := by
      simpa using (hasDerivAt_id s).mul_const ⟪gradient g x, Δ⟫
    have h5 : HasDerivAt (fun s : ℝ => L1 / 2 * s ^ 2 * ‖Δ‖ ^ 2)
        (L1 / 2 * (2 * s) * ‖Δ‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (L1 / 2)).mul_const (‖Δ‖ ^ 2)
      simpa using this
    exact (h2.sub h4).sub h5
  have hanti : AntitoneOn
      (fun s : ℝ => g (x + s • Δ) - s * ⟪gradient g x, Δ⟫ - L1 / 2 * s ^ 2 * ‖Δ‖ ^ 2)
      (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · intro s _; exact (hder s).continuousAt.continuousWithinAt
    · intro s _; exact (hder s).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs' : 0 < s := hs
      have e1 : ⟪gradient g (x + s • Δ), Δ⟫ - ⟪gradient g x, Δ⟫ =
          ⟪gradient g (x + s • Δ) - gradient g x, Δ⟫ := by
        rw [inner_sub_left]
      have e2 : ⟪gradient g (x + s • Δ) - gradient g x, Δ⟫ ≤
          ‖gradient g (x + s • Δ) - gradient g x‖ * ‖Δ‖ :=
        real_inner_le_norm _ _
      have e3 : ‖gradient g (x + s • Δ) - gradient g x‖ ≤ L1 * (s * ‖Δ‖) := by
        have := hgL (x + s • Δ) x
        rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs'.le] at this
      have e4 : 0 ≤ ‖Δ‖ := norm_nonneg _
      have e5 := mul_le_mul_of_nonneg_right e3 e4
      nlinarith
  have := hanti (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 ht) ht
  simp only [zero_smul, add_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero] at this
  linarith

theorem aux_sds_lam {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hD : IsProperClosedConvex D h) (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) (hq : 0 ≤ ⟪H Δ, Δ⟫)
    (hΔ : IsSearchDirection g D h x H Δ) :
    predDecrease g h x Δ ≤ -⟪H Δ, Δ⟫ := by
  obtain ⟨_, hDc, hhc, _⟩ := hD
  obtain ⟨hxΔ, hopt⟩ := hΔ
  have key : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ⟪gradient g x, Δ⟫ + 1 / 2 * ⟪H Δ, Δ⟫ + h (x + Δ) ≤
        s * ⟪gradient g x, Δ⟫ + 1 / 2 * (s * (s * ⟪H Δ, Δ⟫)) +
          ((1 - s) * h x + s * h (x + Δ)) := by
    intro s hs0 hs1
    have hmem : x + s • Δ ∈ D := hDc.add_smul_mem hx hxΔ ⟨hs0, hs1⟩
    have h1 := hopt (s • Δ) hmem
    have h2 : h (x + s • Δ) ≤ (1 - s) * h x + s * h (x + Δ) := by
      have := hhc.2 hx hxΔ (sub_nonneg.2 hs1) hs0 (sub_add_cancel 1 s)
      have e : (1 - s) • x + s • (x + Δ) = x + s • Δ := by module
      rw [e] at this
      simpa [smul_eq_mul] using this
    rw [map_smul, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right] at h1
    linarith
  unfold predDecrease
  by_contra hcon
  push Not at hcon
  have hδpos : 0 < ⟪gradient g x, Δ⟫ + h (x + Δ) - h x + ⟪H Δ, Δ⟫ := by linarith
  have hqδ : 0 < ⟪H Δ, Δ⟫ + (⟪gradient g x, Δ⟫ + h (x + Δ) - h x + ⟪H Δ, Δ⟫) := by linarith
  have hs0 : 0 ≤ ⟪H Δ, Δ⟫ / (⟪H Δ, Δ⟫ + (⟪gradient g x, Δ⟫ + h (x + Δ) - h x + ⟪H Δ, Δ⟫)) :=
    div_nonneg hq hqδ.le
  have hs1 : ⟪H Δ, Δ⟫ / (⟪H Δ, Δ⟫ + (⟪gradient g x, Δ⟫ + h (x + Δ) - h x + ⟪H Δ, Δ⟫)) ≤ 1 := by
    rw [div_le_one hqδ]; linarith
  have hsq : ⟪H Δ, Δ⟫ / (⟪H Δ, Δ⟫ + (⟪gradient g x, Δ⟫ + h (x + Δ) - h x + ⟪H Δ, Δ⟫)) *
      (⟪H Δ, Δ⟫ + (⟪gradient g x, Δ⟫ + h (x + Δ) - h x + ⟪H Δ, Δ⟫)) = ⟪H Δ, Δ⟫ :=
    div_mul_cancel₀ _ hqδ.ne'
  have hk := key _ hs0 hs1
  generalize ⟪H Δ, Δ⟫ / (⟪H Δ, Δ⟫ + (⟪gradient g x, Δ⟫ + h (x + Δ) - h x + ⟪H Δ, Δ⟫)) = s
    at hs0 hs1 hsq hk
  generalize hδdef : ⟪gradient g x, Δ⟫ + h (x + Δ) - h x + ⟪H Δ, Δ⟫ = δ at hδpos hqδ hsq
  have hA : ⟪gradient g x, Δ⟫ = δ - ⟪H Δ, Δ⟫ - h (x + Δ) + h x := by linarith
  rw [hA] at hk
  have hu : 0 < 1 - s := by
    by_contra hc
    push Not at hc
    nlinarith
  have e : (1 - s) * ⟪H Δ, Δ⟫ = s * δ := by linarith
  have e2 : (1 - s) * (1 + s) * ⟪H Δ, Δ⟫ = (1 + s) * (s * δ) := by rw [← e]; ring
  have hp : 0 < δ * (1 - s) * (2 - s) := mul_pos (mul_pos hδpos hu) (by linarith)
  nlinarith

end ProxNewton.Exact

open ProxNewton.Exact

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 m α : ℝ)
    (hg : ContDiff ℝ 1 g) (hgc : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hgL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hD : IsProperClosedConvex D h) (hm : 0 < m) (hα : 0 < α) (hα2 : α < 1 / 2)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ D) (hH : IsLowerBounded H m) (hΔ : IsSearchDirection g D h x H Δ) :
    ∀ t : ℝ, 0 < t → t ≤ 1 → L1 * t ≤ 2 * m * (1 - α) →
      SufficientDescent g D h α x Δ t := by
  intro t ht0 ht1 hLt
  have hq : m * ‖Δ‖ ^ 2 ≤ ⟪H Δ, Δ⟫ := hH.2 Δ
  have hN : 0 ≤ ‖Δ‖ ^ 2 := by positivity
  have hq0 : 0 ≤ ⟪H Δ, Δ⟫ := le_trans (by positivity) hq
  have hlam := aux_sds_lam g D h hD x H Δ hx hq0 hΔ
  have hdesc := aux_sds_descent g L1 hg hgL x Δ t ht0.le
  obtain ⟨_, hDc, hhc, _⟩ := hD
  have hmem : x + t • Δ ∈ D := hDc.add_smul_mem hx hΔ.1 ⟨ht0.le, ht1⟩
  have hh : h (x + t • Δ) ≤ (1 - t) * h x + t * h (x + Δ) := by
    have := hhc.2 hx hΔ.1 (sub_nonneg.2 ht1) ht0.le (sub_add_cancel 1 t)
    have e : (1 - t) • x + t • (x + Δ) = x + t • Δ := by module
    rw [e] at this
    simpa [smul_eq_mul] using this
  unfold SufficientDescent compositeObj
  simp only [hmem, if_true]
  rw [EReal.coe_le_coe_iff]
  unfold predDecrease at hlam ⊢
  have h1a : 0 ≤ 1 - α := by linarith
  have k1 := mul_le_mul_of_nonneg_left hlam h1a
  have k2 := mul_le_mul_of_nonneg_left hq h1a
  have k3 := mul_le_mul_of_nonneg_right hLt hN
  have key : (1 - α) * (⟪gradient g x, Δ⟫ + h (x + Δ) - h x) + L1 * t * ‖Δ‖ ^ 2 / 2 ≤ 0 := by
    nlinarith
  have k4 := mul_le_mul_of_nonneg_left key ht0.le
  nlinarith
