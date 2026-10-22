-- Prove2me | solution 1 for PenaltyLag.Exact.stationary_at_dual_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:18:49.516912+00:00
-- url     : https://prove2.me/submissions/509edb63-8037-4022-bff0-64d1ec1d4d94

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


theorem stat_core {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : Mult m) (hybar : IsDualOptimal X f₀ f r ybar)
    (xbar : E) (hxbar : xbar ∈ X)
    (hmin : ∀ x ∈ X, Lr f₀ f r xbar ybar ≤ Lr f₀ f r x ybar) :
    HasGradientAt (fun y => Lr f₀ f r xbar y) 0 ybar ∧ ∀ y, Lr f₀ f r xbar y ≤ Lr f₀ f r xbar ybar := by
  have key := pl_key X hX f₀ f hf₀ hf r hr ybar xbar hxbar hmin
  have hgr : gr X f₀ f r ybar = ((Lr f₀ f r xbar ybar : ℝ) : EReal) :=
    le_antisymm (iInf₂_le xbar hxbar)
      (le_iInf₂ fun x hx => EReal.coe_le_coe_iff.2 (hmin x hx))
  have hle : ∀ y : Mult m, Lr f₀ f r xbar ybar + ∑ i, ((y i - ybar i) * max (f i xbar) (-ybar i / (2 * r)))
        - ∑ i, (y i - ybar i) ^ 2 / (4 * r) ≤ Lr f₀ f r xbar ybar := by
    intro y
    have h1 : gr X f₀ f r y ≤ gr X f₀ f r ybar := by
      rw [hybar.2]; exact le_iSup (fun y => gr X f₀ f r y) y
    have h2 : ((Lr f₀ f r xbar ybar + ∑ i, ((y i - ybar i) * max (f i xbar) (-ybar i / (2 * r)))
        - ∑ i, (y i - ybar i) ^ 2 / (4 * r) : ℝ) : EReal) ≤ gr X f₀ f r y :=
      le_iInf₂ fun x hx => EReal.coe_le_coe_iff.2 (key x hx y)
    rw [hgr] at h1
    exact EReal.coe_le_coe_iff.1 (h2.trans h1)
  set ub : Fin m → ℝ := fun i => max (f i xbar) (-ybar i / (2 * r)) with hub
  have hub0 : ∀ i, ub i = 0 := by
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
  have hf0 : ∀ i, f i xbar ≤ 0 := fun i => by
    have := hub0 i
    have h2 : f i xbar ≤ ub i := le_max_left _ _
    linarith
  have hLv : Lr f₀ f r xbar ybar = f₀ xbar := by
    rw [pl_L_eq f₀ f hr xbar ybar]
    have : ∀ i, r * (max (f i xbar) (-ybar i / (2 * r))) ^ 2 + ybar i * max (f i xbar) (-ybar i / (2 * r)) = 0 := fun i => by
      have := hub0 i
      simp only [hub] at this
      rw [this]; ring
    simp [this]
  refine ⟨?_, ?_⟩
  · have hbd : ∀ y : Mult m, |Lr f₀ f r xbar y - Lr f₀ f r xbar ybar| ≤ ‖y - ybar‖ ^ 2 / (4 * r) := by
      intro y
      have hup : Lr f₀ f r xbar y ≤ Lr f₀ f r xbar ybar := by
        have := pl_L_le f₀ f hr xbar y (fun _ => 0) hf0
        rw [hLv]
        simpa using this
      have hlo := key xbar hxbar y
      have hz : ∑ i, ((y i - ybar i) * max (f i xbar) (-ybar i / (2 * r))) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          have := hub0 i
          simp only [hub] at this
          rw [this]; ring
      rw [hz] at hlo
      have hn : ‖y - ybar‖ ^ 2 = ∑ i, (y i - ybar i) ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
        exact Finset.sum_congr rfl fun i _ => by simp [Real.norm_eq_abs, sq_abs]
      have hn2 : ∑ i, (y i - ybar i) ^ 2 / (4 * r) = ‖y - ybar‖ ^ 2 / (4 * r) := by
        rw [hn, Finset.sum_div]
      rw [abs_le]
      constructor <;> linarith
    rw [hasGradientAt_iff_hasFDerivAt, map_zero, hasFDerivAt_iff_tendsto]
    have hT : Filter.Tendsto (fun y : Mult m => ‖y - ybar‖ / (4 * r)) (nhds ybar) (nhds 0) := by
      have : Filter.Tendsto (fun y : Mult m => ‖y - ybar‖) (nhds ybar) (nhds 0) := by
        have h := ((continuous_id.sub (continuous_const (y := ybar))).norm).tendsto ybar
        simpa using h
      simpa using this.div_const (4 * r)
    refine squeeze_zero (fun _ => by positivity) (fun y => ?_) hT
    by_cases h0 : ‖y - ybar‖ = 0
    · simp [h0]
    · have hp : 0 < ‖y - ybar‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      simp only [zero_apply, sub_zero, Real.norm_eq_abs]
      have := hbd y
      rw [inv_mul_le_iff₀ hp]
      calc |Lr f₀ f r xbar y - Lr f₀ f r xbar ybar| ≤ ‖y - ybar‖ ^ 2 / (4 * r) := this
        _ = ‖y - ybar‖ * (‖y - ybar‖ / (4 * r)) := by ring
  · intro y
    have := pl_L_le f₀ f hr xbar y (fun _ => 0) hf0
    rw [hLv]
    simpa using this

end PenaltyLag.Exact

open PenaltyLag.Exact


theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (ybar : PenaltyLag.Asymptotic.Mult m) (hybar : IsDualOptimal X f₀ f r ybar)
    (xbar : E) (hxbar : xbar ∈ X) (hmin : ∀ x ∈ X, PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar ≤ PenaltyLag.Asymptotic.Lr f₀ f r x ybar) :
    HasGradientAt (fun y => PenaltyLag.Asymptotic.Lr f₀ f r xbar y) 0 ybar ∧ ∀ y, PenaltyLag.Asymptotic.Lr f₀ f r xbar y ≤ PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar := by
  exact stat_core X hX f₀ f hf₀ hf r hr ybar hybar xbar hxbar hmin
