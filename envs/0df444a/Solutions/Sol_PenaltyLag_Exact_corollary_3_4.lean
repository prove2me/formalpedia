-- Prove2me | solution 1 for PenaltyLag.Exact.corollary_3_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:23:21.753392+00:00
-- url     : https://prove2.me/submissions/acfd065c-81cd-46d7-9c99-b1b8c0a554a0

import Mathlib
import Definitions.Def_PenaltyLag_Exact_Basic



namespace PenaltyLag.Exact

open PenaltyLag.Asymptotic

lemma pl_term_le {r y f u : ℝ} (hr : 0 < r) (hu : f ≤ u) :
    (1 / (4 * r)) * (theta (y + 2 * r * f) ^ 2 - y ^ 2) ≤ r * u ^ 2 + y * u := by
  unfold theta
  have h4 : (0:ℝ) < 4 * r := by positivity
  rw [one_div, inv_mul_le_iff₀ h4]
  rcases le_total 0 (y + 2 * r * f) with h | h
  · rw [max_eq_right h]
    have h1 : 0 ≤ 2 * r * (u - f) := by
      have : 0 ≤ u - f := by linarith
      positivity
    have h2 : 0 ≤ 2 * r * u + 2 * r * f + 2 * y := by nlinarith
    nlinarith [mul_nonneg h1 h2]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg (2 * r * u + y)]

lemma pl_term_eq {r y f : ℝ} (hr : 0 < r) :
    (1 / (4 * r)) * (theta (y + 2 * r * f) ^ 2 - y ^ 2) =
      r * (max f (-y / (2 * r))) ^ 2 + y * (max f (-y / (2 * r))) := by
  unfold theta
  have h2 : (0:ℝ) < 2 * r := by positivity
  rcases le_total f (-y / (2 * r)) with h | h
  · rw [max_eq_right h]
    have h' : y + 2 * r * f ≤ 0 := by
      have := (le_div_iff₀ h2).1 h
      linarith
    rw [max_eq_left h']
    field_simp
    ring
  · rw [max_eq_left h]
    have h' : 0 ≤ y + 2 * r * f := by
      have := (div_le_iff₀ h2).1 h
      linarith
    rw [max_eq_right h']
    field_simp
    ring

lemma pl_L_le {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (x : E) (y : Mult m) (u : Fin m → ℝ) (hu : ∀ i, f i x ≤ u i) :
    Lr f₀ f r x y ≤ f₀ x + ∑ i, (r * u i ^ 2 + y i * u i) := by
  unfold Lr
  rw [Finset.mul_sum]
  exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => pl_term_le hr (hu i))

lemma pl_L_eq {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (x : E) (y : Mult m) :
    Lr f₀ f r x y = f₀ x + ∑ i, (r * (max (f i x) (-y i / (2 * r))) ^ 2
      + y i * (max (f i x) (-y i / (2 * r)))) := by
  unfold Lr
  rw [Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => pl_term_eq hr)

/-- the key lower bound -/
theorem pl_key {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : Mult m) (xbar : E) (hxbar : xbar ∈ X)
    (hmin : ∀ x ∈ X, Lr f₀ f r xbar ybar ≤ Lr f₀ f r x ybar) :
    ∀ x ∈ X, ∀ y : Mult m,
      Lr f₀ f r xbar ybar + ∑ i, ((y i - ybar i) * max (f i xbar) (-ybar i / (2 * r)))
        - ∑ i, (y i - ybar i) ^ 2 / (4 * r) ≤ Lr f₀ f r x y := by
  intro x hx y
  set ub : Fin m → ℝ := fun i => max (f i xbar) (-ybar i / (2 * r)) with hub
  have hvub : Lr f₀ f r xbar ybar = f₀ xbar + ∑ i, (r * ub i ^ 2 + ybar i * ub i) :=
    pl_L_eq f₀ f hr xbar ybar
  -- strong convexity
  have step : ∀ x ∈ X, ∀ u : Fin m → ℝ, (∀ i, f i x ≤ u i) →
      Lr f₀ f r xbar ybar + ∑ i, r * (u i - ub i) ^ 2 ≤ f₀ x + ∑ i, (r * u i ^ 2 + ybar i * u i) := by
    intro x hx u hu
    set A : ℝ := (f₀ x - f₀ xbar) + ∑ i, (2 * r * ub i * (u i - ub i) + ybar i * (u i - ub i)) with hA
    set K : ℝ := ∑ i, r * (u i - ub i) ^ 2 with hK
    have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
    have key : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ A + s * K := by
      intro s hs hs1
      have hxs : (1 - s) • xbar + s • x ∈ X := hX hxbar hx (by linarith) hs.le (by ring)
      have hfs : ∀ i, f i ((1 - s) • xbar + s • x) ≤ (1 - s) * ub i + s * u i := by
        intro i
        have h1 := (hf i).2 hxbar hx (show (0:ℝ) ≤ 1 - s by linarith) hs.le (by ring)
        simp only [smul_eq_mul] at h1
        have h2 : f i xbar ≤ ub i := le_max_left _ _
        have h3 := hu i
        nlinarith
      have h1 := hmin _ hxs
      have h2 := pl_L_le f₀ f hr ((1 - s) • xbar + s • x) ybar (fun i => (1 - s) * ub i + s * u i) hfs
      have h3 := hf₀.2 hxbar hx (show (0:ℝ) ≤ 1 - s by linarith) hs.le (by ring)
      simp only [smul_eq_mul] at h3
      have hsum : ∑ i, (r * ((1 - s) * ub i + s * u i) ^ 2 + ybar i * ((1 - s) * ub i + s * u i))
          = ∑ i, (r * ub i ^ 2 + ybar i * ub i)
            + s * (∑ i, (2 * r * ub i * (u i - ub i) + ybar i * (u i - ub i))) + s ^ 2 * K := by
        rw [hK, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsum] at h2
      rw [hvub] at h1
      have : 0 ≤ s * (A + s * K) := by rw [hA]; nlinarith
      exact nonneg_of_mul_nonneg_right this hs |>.trans' le_rfl
    have hA0 : 0 ≤ A := by
      by_contra hneg
      push Not at hneg
      have hd : 0 < 2 * (K + 1) := by linarith
      set s : ℝ := min 1 (-A / (2 * (K + 1))) with hs
      have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hd)
      have hs1 : s ≤ 1 := min_le_left _ _
      have hs2 : s ≤ -A / (2 * (K + 1)) := min_le_right _ _
      have := key s hs0 hs1
      have h5 : s * (2 * (K + 1)) ≤ -A := (le_div_iff₀ hd).1 hs2
      nlinarith
    have : f₀ x + ∑ i, (r * u i ^ 2 + ybar i * u i) - (Lr f₀ f r xbar ybar + K) = A := by
      rw [hvub, hA, hK, ← sub_eq_zero]
      have e : ∑ i, (r * u i ^ 2 + ybar i * u i) - ∑ i, (r * ub i ^ 2 + ybar i * ub i)
          - ∑ i, r * (u i - ub i) ^ 2
          = ∑ i, (2 * r * ub i * (u i - ub i) + ybar i * (u i - ub i)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith
    linarith
  -- lower bound
  set ustar : Fin m → ℝ := fun i => max (f i x) (-y i / (2 * r)) with hustar
  have hy : Lr f₀ f r x y = f₀ x + ∑ i, (r * ustar i ^ 2 + y i * ustar i) := pl_L_eq f₀ f hr x y
  have hst := step x hx ustar (fun i => le_max_left _ _)
  have e : ∑ i, (r * ustar i ^ 2 + y i * ustar i)
      = ∑ i, (r * ustar i ^ 2 + ybar i * ustar i) + ∑ i, ((y i - ybar i) * ustar i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hq : ∑ i, ((y i - ybar i) * ub i) - ∑ i, (y i - ybar i) ^ 2 / (4 * r)
      ≤ ∑ i, r * (ustar i - ub i) ^ 2 + ∑ i, ((y i - ybar i) * ustar i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h4 : (0:ℝ) < 4 * r := by positivity
    have : (y i - ybar i) * ub i - (y i - ybar i) ^ 2 / (4 * r)
        ≤ r * (ustar i - ub i) ^ 2 + (y i - ybar i) * ustar i := by
      have : r * (ustar i - ub i) ^ 2 + (y i - ybar i) * (ustar i - ub i)
          + (y i - ybar i) ^ 2 / (4 * r) = r * ((ustar i - ub i) + (y i - ybar i) / (2 * r)) ^ 2 := by
        field_simp
        ring
      nlinarith [sq_nonneg ((ustar i - ub i) + (y i - ybar i) / (2 * r)), mul_nonneg hr.le (sq_nonneg ((ustar i - ub i) + (y i - ybar i) / (2 * r)))]
    exact this
  rw [hy, e]
  linarith



lemma pl_ub_zero {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (ybar : Mult m) (xbar : E)
    (hle : ∀ y : Mult m, Lr f₀ f r xbar ybar + ∑ i, ((y i - ybar i) * max (f i xbar) (-ybar i / (2 * r)))
        - ∑ i, (y i - ybar i) ^ 2 / (4 * r) ≤ Lr f₀ f r xbar ybar) :
    ∀ i, max (f i xbar) (-ybar i / (2 * r)) = 0 := by
  set ub : Fin m → ℝ := fun i => max (f i xbar) (-ybar i / (2 * r)) with hub
  have h := hle (ybar + WithLp.toLp 2 (fun i => 2 * r * ub i))
  simp only [PiLp.add_apply, add_sub_cancel_left] at h
  have e1 : ∑ i, 2 * r * ub i * max (f i xbar) (-ybar i / (2 * r)) = ∑ i, 2 * r * ub i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [show max (f i xbar) (-ybar i / (2 * r)) = ub i from rfl]; ring
  have e2 : ∑ i, (2 * r * ub i) ^ 2 / (4 * r) = ∑ i, r * ub i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by field_simp; ring
  rw [e1, e2] at h
  have hs : ∑ i, ub i ^ 2 ≤ 0 := by
    have : 2 * r * ∑ i, ub i ^ 2 - r * ∑ i, ub i ^ 2 ≤ 0 := by
      rw [Finset.mul_sum, Finset.mul_sum]; linarith
    have h' : r * ∑ i, ub i ^ 2 ≤ 0 := by linarith
    exact nonpos_of_mul_nonpos_right h' hr
  intro i
  have h0 : ∑ i, ub i ^ 2 = 0 :=
    le_antisymm hs (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ub i))).1 h0 i (Finset.mem_univ i)
  exact pow_eq_zero_iff (two_ne_zero) |>.1 this

lemma pl_term_ge {r y f : ℝ} (hr : 0 < r) (hy : 0 ≤ y) :
    y * f ≤ (1 / (4 * r)) * (theta (y + 2 * r * f) ^ 2 - y ^ 2) := by
  unfold theta
  have h4 : (0:ℝ) < 4 * r := by positivity
  rw [one_div, le_inv_mul_iff₀ h4]
  rcases le_total 0 (y + 2 * r * f) with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg f, mul_pos hr hr]
  · rw [max_eq_left h]
    have h' : 0 ≤ -(y + 2 * r * f) := by linarith
    nlinarith [mul_nonneg hy h', sq_nonneg y]

lemma pl_theta_sq_le {r y f : ℝ} (hr : 0 < r) (hf : f ≤ 0) :
    theta (y + 2 * r * f) ^ 2 ≤ y ^ 2 := by
  unfold theta
  have : 2 * r * f ≤ 0 := by nlinarith
  rcases le_total 0 (y + 2 * r * f) with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith [sq_nonneg y]

lemma pl_L_feas {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (x : E) (y : Mult m) (hx : ∀ i, f i x ≤ 0) : Lr f₀ f r x y ≤ f₀ x := by
  have := pl_L_le f₀ f hr x y (fun _ => 0) hx
  simpa using this

lemma pl_L_ge_psi {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (x : E) (y : Mult m) (hy : ∀ i, 0 ≤ y i) :
    f₀ x + ∑ i, y i * f i x ≤ Lr f₀ f r x y := by
  unfold Lr
  rw [Finset.mul_sum]
  exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => pl_term_ge hr (hy i))

lemma pl_comb {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : Mult m) (q : ℝ)
    (hq : ∀ z ∈ X, q ≤ Lr f₀ f r z ybar) (x' : E) (hx' : x' ∈ X) (hfe : ∀ i, f i x' ≤ 0)
    (x : E) (hx : x ∈ X) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    q ≤ (1 - s) * f₀ x' + s * (f₀ x + ∑ i, ybar i * f i x) + s ^ 2 * (r * ∑ i, f i x ^ 2) := by
  have hxs : (1 - s) • x' + s • x ∈ X := hX hx' hx (by linarith) hs0.le (by ring)
  have hfs : ∀ i, f i ((1 - s) • x' + s • x) ≤ s * f i x := by
    intro i
    have h1 := (hf i).2 hx' hx (show (0:ℝ) ≤ 1 - s by linarith) hs0.le (by ring)
    simp only [smul_eq_mul] at h1
    have := hfe i
    nlinarith
  have h1 := hq _ hxs
  have h2 := pl_L_le f₀ f hr ((1 - s) • x' + s • x) ybar (fun i => s * f i x) hfs
  have h3 := hf₀.2 hx' hx (show (0:ℝ) ≤ 1 - s by linarith) hs0.le (by ring)
  simp only [smul_eq_mul] at h3
  have hsum : ∑ i, (r * (s * f i x) ^ 2 + ybar i * (s * f i x))
      = s ^ 2 * (r * ∑ i, f i x ^ 2) + s * ∑ i, ybar i * f i x := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum] at h2
  nlinarith

lemma pl_lim (q ψ K : ℝ) (hK : 0 ≤ K)
    (h : ∀ ε : ℝ, 0 < ε → ∀ s : ℝ, 0 < s → s ≤ 1 → q ≤ (1 - s) * (q + ε) + s * ψ + s ^ 2 * K) :
    q ≤ ψ := by
  by_contra hn
  push Not at hn
  set δ := q - ψ with hδ
  have hδ0 : 0 < δ := by linarith
  have hd : 0 < 2 * (K + 1) := by linarith
  set s : ℝ := min 1 (δ / (2 * (K + 1))) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos hδ0 hd)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ δ / (2 * (K + 1)) := min_le_right _ _
  have h5 : s * (2 * (K + 1)) ≤ δ := (le_div_iff₀ hd).1 hs2
  have h6 := h (s * δ / 4) (by positivity) s hs0 hs1
  have h7 : s * K ≤ δ / 2 := by nlinarith
  have h8 : s ^ 2 * K ≤ s * (δ / 2) := by nlinarith
  nlinarith [mul_pos hs0 hδ0, mul_nonneg hs0.le (show 0 ≤ s * δ / 4 by positivity)]


lemma pl_L_kt {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) {r : ℝ} (hr : 0 < r)
    (xbar : E) (ybar : Mult m)
    (h : ∀ i, 0 ≤ ybar i ∧ f i xbar ≤ 0 ∧ ybar i * f i xbar = 0) :
    Lr f₀ f r xbar ybar = f₀ xbar := by
  unfold Lr
  have : ∀ i, theta (ybar i + 2 * r * f i xbar) ^ 2 - ybar i ^ 2 = 0 := by
    intro i
    obtain ⟨h1, h2, h3⟩ := h i
    unfold theta
    rcases mul_eq_zero.1 h3 with h4 | h4
    · rw [h4]
      have : (0:ℝ) + 2 * r * f i xbar ≤ 0 := by nlinarith
      rw [max_eq_left this]; ring
    · rw [h4]
      simp only [mul_zero, add_zero]
      rw [max_eq_right h1]; ring
  simp [this]

theorem pl_saddle_iff_KT {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (xbar : E) (ybar : Mult m) :
    IsSaddle X f₀ f r xbar ybar ↔ KuhnTuckerConditions X f₀ f xbar ybar := by
  have h2r : (0:ℝ) < 2 * r := by positivity
  constructor
  · rintro ⟨hx, hmax, hmin⟩
    have key := pl_key X hX f₀ f hf₀ hf r hr ybar xbar hx hmin
    have hub0 := pl_ub_zero f₀ f hr ybar xbar (fun y => (key xbar hx y).trans (hmax y))
    have hcomp : ∀ i, 0 ≤ ybar i ∧ f i xbar ≤ 0 ∧ ybar i * f i xbar = 0 := by
      intro i
      have h0 := hub0 i
      have a1 : f i xbar ≤ 0 := by
        have := le_max_left (f i xbar) (-ybar i / (2 * r)); rw [h0] at this; exact this
      have a2 : 0 ≤ ybar i := by
        have := le_max_right (f i xbar) (-ybar i / (2 * r)); rw [h0] at this
        have := (div_le_iff₀ h2r).1 this
        linarith
      refine ⟨a2, a1, ?_⟩
      rcases max_choice (f i xbar) (-ybar i / (2 * r)) with h | h
      · rw [h] at h0; rw [h0, mul_zero]
      · rw [h] at h0
        have : ybar i = 0 := by
          have := (div_eq_zero_iff.1 h0).resolve_right h2r.ne'
          linarith
        rw [this, zero_mul]
    have hLv := pl_L_kt f₀ f hr xbar ybar hcomp
    have hsum0 : ∑ i, ybar i * f i xbar = 0 :=
      Finset.sum_eq_zero fun i _ => (hcomp i).2.2
    refine ⟨hcomp, hx, fun x hx' => ?_⟩
    have hq : ∀ z ∈ X, f₀ xbar ≤ Lr f₀ f r z ybar := fun z hz => hLv ▸ hmin z hz
    have : f₀ xbar ≤ f₀ x + ∑ i, ybar i * f i x := by
      refine pl_lim (f₀ xbar) _ (r * ∑ i, f i x ^ 2) (by positivity) ?_
      intro ε hε s hs0 hs1
      have := pl_comb X hX f₀ f hf₀ hf r hr ybar (f₀ xbar) hq xbar hx (fun i => (hcomp i).2.1) x hx' s hs0 hs1
      nlinarith
    rw [hsum0, add_zero]
    exact this
  · rintro ⟨hcomp, hx, hmin⟩
    have hLv := pl_L_kt f₀ f hr xbar ybar hcomp
    have hsum0 : ∑ i, ybar i * f i xbar = 0 :=
      Finset.sum_eq_zero fun i _ => (hcomp i).2.2
    refine ⟨hx, fun y => ?_, fun x hx' => ?_⟩
    · rw [hLv]
      exact pl_L_feas f₀ f hr xbar y (fun i => (hcomp i).2.1)
    · rw [hLv]
      have h1 := pl_L_ge_psi f₀ f hr x ybar (fun i => (hcomp i).1)
      have h2 := hmin x hx'
      rw [hsum0, add_zero] at h2
      linarith

lemma pl_L0_pos {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (x : E) (y : Mult m)
    (hy : ∀ i, 0 ≤ y i) : L0 f₀ f x y = ((f₀ x + ∑ i, y i * f i x : ℝ) : EReal) := by
  unfold L0; rw [if_pos hy]

lemma pl_L0_neg {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (x : E) (y : Mult m)
    (hy : ¬ ∀ i, 0 ≤ y i) : L0 f₀ f x y = ⊥ := by
  unfold L0; rw [if_neg hy]

theorem pl_saddle0_iff_KT {E : Type*} {m : ℕ}
    (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (xbar : E) (ybar : Mult m) :
    IsSaddle0 X f₀ f xbar ybar ↔ KuhnTuckerConditions X f₀ f xbar ybar := by
  constructor
  · rintro ⟨hx, hmax, hmin⟩
    have hy0 : ∀ i, 0 ≤ ybar i := by
      by_contra hn
      have h := hmax 0
      rw [pl_L0_neg f₀ f xbar ybar hn, pl_L0_pos f₀ f xbar 0 (fun i => le_refl _)] at h
      exact absurd h (by simp)
    have hineq : ∀ y : Mult m, (∀ i, 0 ≤ y i) →
        ∑ i, y i * f i xbar ≤ ∑ i, ybar i * f i xbar := by
      intro y hy
      have h := hmax y
      rw [pl_L0_pos f₀ f xbar y hy, pl_L0_pos f₀ f xbar ybar hy0] at h
      have := EReal.coe_le_coe_iff.1 h
      linarith
    have hf0 : ∀ i, f i xbar ≤ 0 := by
      intro i
      have h := hineq (ybar + WithLp.toLp 2 (fun j => if j = i then 1 else 0))
        (fun j => by
          simp only [PiLp.add_apply]
          have := hy0 j
          split_ifs <;> linarith)
      simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      linarith
    have hge : 0 ≤ ∑ i, ybar i * f i xbar := by
      have := hineq 0 (fun i => le_refl _)
      simpa using this
    have hle : ∑ i, ybar i * f i xbar ≤ 0 :=
      Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy0 i) (hf0 i)
    have hz : ∑ i, ybar i * f i xbar = 0 := le_antisymm hle hge
    have hall := (Finset.sum_eq_zero_iff_of_nonpos
      (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy0 i) (hf0 i))).1 hz
    refine ⟨fun i => ⟨hy0 i, hf0 i, hall i (Finset.mem_univ i)⟩, hx, fun x hx' => ?_⟩
    have h := hmin x hx'
    rw [pl_L0_pos f₀ f xbar ybar hy0, pl_L0_pos f₀ f x ybar hy0] at h
    exact EReal.coe_le_coe_iff.1 h
  · rintro ⟨hcomp, hx, hmin⟩
    have hy0 : ∀ i, 0 ≤ ybar i := fun i => (hcomp i).1
    have hsum0 : ∑ i, ybar i * f i xbar = 0 :=
      Finset.sum_eq_zero fun i _ => (hcomp i).2.2
    refine ⟨hx, fun y => ?_, fun x hx' => ?_⟩
    · by_cases hy : ∀ i, 0 ≤ y i
      · rw [pl_L0_pos f₀ f xbar y hy, pl_L0_pos f₀ f xbar ybar hy0]
        refine EReal.coe_le_coe_iff.2 ?_
        have : ∑ i, y i * f i xbar ≤ 0 :=
          Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy i) (hcomp i).2.1
        linarith
      · rw [pl_L0_neg f₀ f xbar y hy]
        exact bot_le
    · rw [pl_L0_pos f₀ f xbar ybar hy0, pl_L0_pos f₀ f x ybar hy0]
      exact EReal.coe_le_coe_iff.2 (hmin x hx')


lemma pl_gr_le_primal {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    {r : ℝ} (hr : 0 < r) (y : Mult m) : gr X f₀ f r y ≤ primalValue X f₀ f := by
  unfold primalValue gr
  refine le_iInf₂ fun x hx => le_iInf fun hfe => ?_
  exact (iInf₂_le x hx).trans (EReal.coe_le_coe_iff.2 (pl_L_feas f₀ f hr x y hfe))

theorem pl_kt_fwd {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : Mult m)
    (h : ⊥ < gr X f₀ f r ybar ∧ gr X f₀ f r ybar = primalValue X f₀ f) :
    ⊥ < g0 X f₀ f ybar ∧ g0 X f₀ f ybar = primalValue X f₀ f := by
  obtain ⟨hbot, hgp⟩ := h
  obtain ⟨x₀, hx₀⟩ := hXne
  have hltop : gr X f₀ f r ybar < ⊤ :=
    lt_of_le_of_lt (iInf₂_le x₀ hx₀) (EReal.coe_lt_top _)
  obtain ⟨q, hq⟩ : ∃ q : ℝ, gr X f₀ f r ybar = (q : EReal) :=
    ⟨(gr X f₀ f r ybar).toReal, (EReal.coe_toReal hltop.ne hbot.ne').symm⟩
  have hp : primalValue X f₀ f = (q : EReal) := by rw [← hgp, hq]
  have hqL : ∀ z ∈ X, q ≤ Lr f₀ f r z ybar := by
    intro z hz
    have h1 : gr X f₀ f r ybar ≤ ((Lr f₀ f r z ybar : ℝ) : EReal) := iInf₂_le z hz
    rw [hq] at h1
    exact EReal.coe_le_coe_iff.1 h1
  have hnear : ∀ ε : ℝ, 0 < ε → ∃ x' ∈ X, (∀ i, f i x' ≤ 0) ∧ f₀ x' < q + ε := by
    intro ε hε
    have h1 : primalValue X f₀ f < ((q + ε : ℝ) : EReal) := by
      rw [hp]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    unfold primalValue at h1
    obtain ⟨x', h2⟩ := iInf_lt_iff.1 h1
    obtain ⟨hx', h3⟩ := iInf_lt_iff.1 h2
    obtain ⟨hfe, h4⟩ := iInf_lt_iff.1 h3
    exact ⟨x', hx', hfe, EReal.coe_lt_coe_iff.1 h4⟩
  -- ybar >= 0
  have hy0 : ∀ i, 0 ≤ ybar i := by
    by_contra hn
    push Not at hn
    obtain ⟨j, hj⟩ := hn
    have hjpos : 0 < ybar j ^ 2 / (4 * r) := by
      have : 0 < ybar j ^ 2 := by nlinarith
      positivity
    obtain ⟨x', hx', hfe, hlt⟩ := hnear _ hjpos
    have hterm : ∀ i, theta (ybar i + 2 * r * f i x') ^ 2 - ybar i ^ 2 ≤ 0 := fun i => by
      have := pl_theta_sq_le (y := ybar i) hr (hfe i)
      linarith
    have htj : theta (ybar j + 2 * r * f j x') ^ 2 - ybar j ^ 2 = - ybar j ^ 2 := by
      have : ybar j + 2 * r * f j x' < 0 := by
        have := hfe j
        nlinarith
      unfold theta
      rw [max_eq_left this.le]; ring
    have hsum : ∑ i, (theta (ybar i + 2 * r * f i x') ^ 2 - ybar i ^ 2) ≤ - ybar j ^ 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), htj]
      have : ∑ i ∈ Finset.univ.erase j, (theta (ybar i + 2 * r * f i x') ^ 2 - ybar i ^ 2) ≤ 0 :=
        Finset.sum_nonpos fun i _ => hterm i
      linarith
    have hL : Lr f₀ f r x' ybar ≤ f₀ x' - ybar j ^ 2 / (4 * r) := by
      unfold Lr
      have h4 : (0:ℝ) < 4 * r := by positivity
      have : (1 / (4 * r)) * ∑ i, (theta (ybar i + 2 * r * f i x') ^ 2 - ybar i ^ 2)
          ≤ (1 / (4 * r)) * (- ybar j ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have e : (1 / (4 * r)) * (- ybar j ^ 2) = - (ybar j ^ 2 / (4 * r)) := by ring
      linarith
    have := hqL x' hx'
    linarith
  -- psi >= q
  have hpsi : ∀ x ∈ X, q ≤ f₀ x + ∑ i, ybar i * f i x := by
    intro x hx
    refine pl_lim q _ (r * ∑ i, f i x ^ 2) (by positivity) ?_
    intro ε hε s hs0 hs1
    obtain ⟨x', hx', hfe, hlt⟩ := hnear ε hε
    have := pl_comb X hX f₀ f hf₀ hf r hr ybar q hqL x' hx' hfe x hx s hs0 hs1
    have h1 : 0 ≤ 1 - s := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlt.le h1]
  refine ⟨?_, ?_⟩
  · have : (q : EReal) ≤ g0 X f₀ f ybar := by
      refine le_iInf₂ fun x hx => ?_
      rw [pl_L0_pos f₀ f x ybar hy0]
      exact EReal.coe_le_coe_iff.2 (hpsi x hx)
    exact lt_of_lt_of_le (EReal.bot_lt_coe q) this
  · rw [hp]
    apply le_antisymm
    · rw [← hp]
      unfold primalValue g0
      refine le_iInf₂ fun x hx => le_iInf fun hfe => ?_
      refine (iInf₂_le x hx).trans ?_
      rw [pl_L0_pos f₀ f x ybar hy0]
      refine EReal.coe_le_coe_iff.2 ?_
      have : ∑ i, ybar i * f i x ≤ 0 :=
        Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hy0 i) (hfe i)
      linarith
    · refine le_iInf₂ fun x hx => ?_
      rw [pl_L0_pos f₀ f x ybar hy0]
      exact EReal.coe_le_coe_iff.2 (hpsi x hx)

theorem pl_kt_bwd {E : Type*} {m : ℕ}
    (X : Set E) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (r : ℝ) (hr : 0 < r) (ybar : Mult m)
    (h : ⊥ < g0 X f₀ f ybar ∧ g0 X f₀ f ybar = primalValue X f₀ f) :
    ⊥ < gr X f₀ f r ybar ∧ gr X f₀ f r ybar = primalValue X f₀ f := by
  obtain ⟨hbot, hgp⟩ := h
  obtain ⟨x₀, hx₀⟩ := hXne
  have hy0 : ∀ i, 0 ≤ ybar i := by
    by_contra hn
    have h1 : g0 X f₀ f ybar ≤ ⊥ := by
      refine (iInf₂_le x₀ hx₀).trans ?_
      rw [pl_L0_neg f₀ f x₀ ybar hn]
    exact absurd (le_bot_iff.1 h1) hbot.ne'
  have hltop : g0 X f₀ f ybar < ⊤ := by
    refine lt_of_le_of_lt (iInf₂_le x₀ hx₀) ?_
    rw [pl_L0_pos f₀ f x₀ ybar hy0]
    exact EReal.coe_lt_top _
  obtain ⟨q, hq⟩ : ∃ q : ℝ, g0 X f₀ f ybar = (q : EReal) :=
    ⟨(g0 X f₀ f ybar).toReal, (EReal.coe_toReal hltop.ne hbot.ne').symm⟩
  have hp : primalValue X f₀ f = (q : EReal) := by rw [← hgp, hq]
  have hpsi : ∀ x ∈ X, q ≤ f₀ x + ∑ i, ybar i * f i x := by
    intro x hx
    have h1 : g0 X f₀ f ybar ≤ L0 f₀ f x ybar := iInf₂_le x hx
    rw [hq, pl_L0_pos f₀ f x ybar hy0] at h1
    exact EReal.coe_le_coe_iff.1 h1
  have hge : (q : EReal) ≤ gr X f₀ f r ybar := by
    refine le_iInf₂ fun x hx => ?_
    exact EReal.coe_le_coe_iff.2 ((hpsi x hx).trans (pl_L_ge_psi f₀ f hr x ybar hy0))
  refine ⟨lt_of_lt_of_le (EReal.bot_lt_coe q) hge, le_antisymm (pl_gr_le_primal X f₀ f hr ybar) ?_⟩
  rw [hp]; exact hge

theorem cor_core {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) :
    (IsKTVector X f₀ f r ybar ↔ IsKTVector0 X f₀ f ybar) ∧
    (IsSaddle X f₀ f r xbar ybar ↔ IsSaddle0 X f₀ f xbar ybar) ∧
    (IsSaddle X f₀ f r xbar ybar ↔ KuhnTuckerConditions X f₀ f xbar ybar) :=
  ⟨⟨fun h => pl_kt_fwd X hX hXne f₀ f hf₀ hf r hr ybar h,
    fun h => pl_kt_bwd X hXne f₀ f r hr ybar h⟩,
   (pl_saddle_iff_KT X hX f₀ f hf₀ hf r hr xbar ybar).trans
     (pl_saddle0_iff_KT X f₀ f xbar ybar).symm,
   pl_saddle_iff_KT X hX f₀ f hf₀ hf r hr xbar ybar⟩

end PenaltyLag.Exact

open PenaltyLag.Exact


theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) :
    (IsKTVector X f₀ f r ybar ↔ IsKTVector0 X f₀ f ybar) ∧
    (IsSaddle X f₀ f r xbar ybar ↔ IsSaddle0 X f₀ f xbar ybar) ∧
    (IsSaddle X f₀ f r xbar ybar ↔ KuhnTuckerConditions X f₀ f xbar ybar) := by
  exact cor_core X hX hXne f₀ f hf₀ hf r hr xbar ybar
