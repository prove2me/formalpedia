-- Prove2me | solution 1 for ProxNewton.Inexact.compGradStep_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:06:29.285827+00:00
-- url     : https://prove2.me/submissions/c92fcc6a-4eb6-4489-97cc-e232bb7fe050

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace
open Filter Topology

/-- If `0 ≤ c + a t` for all `t ∈ (0,1]`, then `0 ≤ c`. -/
theorem aux_cgs_lim (c a : ℝ) (H : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ c + a * t) : 0 ≤ c := by
  by_contra hc
  push Not at hc
  rcases le_or_gt a 0 with ha | ha
  · have := H 1 one_pos le_rfl
    linarith
  · have hac : 0 < a - c := by linarith
    have h1 := H ((-c) / (a - c)) (div_pos (by linarith) hac)
      ((div_le_one hac).2 (by linarith))
    have h2 : c + a * ((-c) / (a - c)) = -c ^ 2 / (a - c) := by
      field_simp
      ring
    rw [h2] at h1
    have : -c ^ 2 / (a - c) < 0 := div_neg_of_neg_of_pos (by nlinarith) hac
    linarith

/-- Variational inequality for a prox point. -/
theorem aux_cgs_prox_vi {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hD : Convex ℝ D) (hconv : ConvexOn ℝ D h)
    {u p : EuclideanSpace ℝ (Fin n)} (hp : IsProxPoint D h u p) :
    ∀ z ∈ D, ⟪u - p, z - p⟫ ≤ h z - h p := by
  intro z hz
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ (h z - h p + ⟪p - u, z - p⟫) + (‖z - p‖ ^ 2 / 2) * t := by
    intro t ht0 ht1
    have hzt : (1 - t) • p + t • z ∈ D := hD hp.1 hz (by linarith) ht0.le (by ring)
    have h1 := hp.2 _ hzt
    have h2 := hconv.2 hp.1 hz (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
    have heq : (1 - t) • p + t • z - u = (p - u) + t • (z - p) := by module
    rw [heq, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
      abs_of_pos ht0] at h1
    simp only [smul_eq_mul] at h2
    have h3 : 0 ≤ t * ((h z - h p + ⟪p - u, z - p⟫) + (‖z - p‖ ^ 2 / 2) * t) := by
      nlinarith
    exact (mul_nonneg_iff_of_pos_left ht0).1 h3
  have := aux_cgs_lim _ _ key
  have hi : ⟪u - p, z - p⟫ = -⟪p - u, z - p⟫ := by
    rw [← inner_neg_left, neg_sub]
  linarith


/-- Firm nonexpansiveness of prox points. -/
theorem aux_cgs_firm {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hD : Convex ℝ D) (hconv : ConvexOn ℝ D h)
    {u u' p q : EuclideanSpace ℝ (Fin n)} (hp : IsProxPoint D h u p)
    (hq : IsProxPoint D h u' q) : ‖p - q‖ ^ 2 ≤ ⟪u - u', p - q⟫ := by
  have h1 := aux_cgs_prox_vi hD hconv hp q hq.1
  have h2 := aux_cgs_prox_vi hD hconv hq p hp.1
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right] at *
  have c1 := real_inner_comm p q
  have c2 := real_inner_comm u q
  have c3 := real_inner_comm u p
  have c4 := real_inner_comm u' q
  have c5 := real_inner_comm u' p
  linarith

/-- First-order optimality condition at a minimizer of `g + h` over `D`. -/
theorem aux_cgs_foc {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Differentiable ℝ g) (hD : Convex ℝ D) (hconv : ConvexOn ℝ D h)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : IsMinimizer g D h xs) :
    ∀ y ∈ D, 0 ≤ h y - h xs + ⟪gradient g xs, y - xs⟫ := by
  intro y hy
  let ψ : ℝ → ℝ := fun t => g (xs + t • (y - xs))
  have hψ : HasDerivAt ψ ⟪gradient g xs, y - xs⟫ 0 := by
    have h1 : HasDerivAt (fun t : ℝ => xs + t • (y - xs)) (y - xs) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - xs)).const_add xs
    have h2 : HasFDerivAt g (fderiv ℝ g (xs + (0:ℝ) • (y - xs))) (xs + (0:ℝ) • (y - xs)) :=
      (hg _).hasFDerivAt
    have := h2.comp_hasDerivAt (0:ℝ) h1
    simp only [zero_smul, add_zero] at this
    rw [inner_gradient_left (𝕜 := ℝ) (f := g) (x := xs) (y := y - xs)]
    exact this
  have hT := hψ.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), -(h y - h xs) ≤ t⁻¹ • (ψ (0 + t) - ψ 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have heq : (1 - t) • xs + t • y = xs + t • (y - xs) := by module
    have hzt : xs + t • (y - xs) ∈ D := by
      have := hD hxs.1 hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
      rwa [heq] at this
    have hmin := hxs.2 _ hzt
    have hc := hconv.2 hxs.1 hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
    rw [heq, smul_eq_mul, smul_eq_mul] at hc
    simp only [ψ, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    nlinarith
  have := ge_of_tendsto hT hev
  linarith

/-- A minimizer is a fixed point of the forward-backward map. -/
theorem aux_cgs_fixed {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Differentiable ℝ g) (hD : Convex ℝ D) (hconv : ConvexOn ℝ D h)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : IsMinimizer g D h xs) :
    IsProxPoint D h (xs - gradient g xs) xs := by
  refine ⟨hxs.1, fun z hz => ?_⟩
  have hb := aux_cgs_foc hg hD hconv hxs z hz
  have e1 : xs - (xs - gradient g xs) = gradient g xs := by abel
  have e2 : z - (xs - gradient g xs) = (z - xs) + gradient g xs := by abel
  rw [e1, e2, norm_add_sq_real]
  have := sq_nonneg ‖z - xs‖
  rw [real_inner_comm] at hb
  nlinarith

open Classical in
/-- Existence of a prox point, given an affine minorant of `h` on `D`. -/
theorem aux_cgs_exists {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : IsProperClosedConvex D h)
    {x0 w : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ D)
    (hmin : ∀ y ∈ D, h x0 + ⟪w, y - x0⟫ ≤ h y) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ p, IsProxPoint D h v p := by
  obtain ⟨-, -, -, hlsc⟩ := hh
  have hq : LowerSemicontinuous
      (fun y : EuclideanSpace ℝ (Fin n) => ((‖y - v‖ ^ 2 / 2 : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
  have hF := LowerSemicontinuous.add' hlsc hq (fun y =>
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
  set F := (fun z : EuclideanSpace ℝ (Fin n) =>
    (fun x => if x ∈ D then (h x : EReal) else ⊤) z + ((‖z - v‖ ^ 2 / 2 : ℝ) : EReal)) with hFdef
  have hFin : ∀ y ∈ D, F y = ((h y + ‖y - v‖ ^ 2 / 2 : ℝ) : EReal) := by
    intro y hy
    simp only [hFdef, if_pos hy, EReal.coe_add]
  have hFout : ∀ y, y ∉ D → F y = ⊤ := by
    intro y hy
    simp only [hFdef, if_neg hy, EReal.top_add_coe]
  set G := ‖w‖ with hGdef
  set b := ‖x0 - v‖ with hbdef
  set R := 2 * G + 2 * b + 1 with hRdef
  have hG : 0 ≤ G := norm_nonneg w
  have hb : 0 ≤ b := norm_nonneg (x0 - v)
  have hK : IsCompact (Metric.closedBall v R) := isCompact_closedBall v R
  have hx0K : x0 ∈ Metric.closedBall v R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith
  obtain ⟨m, hmK, hmmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn ⟨x0, hx0K⟩ hK (hF.lowerSemicontinuousOn _)
  rw [isMinOn_iff] at hmmin
  have hcoer : ∀ z ∈ D, R < ‖z - v‖ → h x0 + ‖x0 - v‖ ^ 2 / 2 ≤ h z + ‖z - v‖ ^ 2 / 2 := by
    intro z hz hR
    have h1 := hmin z hz
    have h2 : -(G * ‖z - x0‖) ≤ ⟪w, z - x0⟫ := by
      have := abs_real_inner_le_norm w (z - x0)
      rw [abs_le] at this
      linarith [this.1]
    have h3 : ‖z - x0‖ ≤ ‖z - v‖ + b := by
      calc ‖z - x0‖ = ‖(z - v) - (x0 - v)‖ := by congr 1; abel
        _ ≤ ‖z - v‖ + ‖x0 - v‖ := norm_sub_le _ _
    have h4 : G * ‖z - x0‖ ≤ G * (‖z - v‖ + b) := mul_le_mul_of_nonneg_left h3 hG
    have h5 : R * (b + 1 / 2) ≤ ‖z - v‖ * (‖z - v‖ / 2 - G) :=
      mul_le_mul hR.le (by linarith) (by positivity) (by linarith)
    have h6 : R * (b + 1 / 2) = 2 * G * b + G + 2 * b ^ 2 + 2 * b + 1 / 2 := by
      rw [hRdef]; ring
    rw [← hbdef]
    nlinarith [mul_nonneg hG hb]
  have hFx0 := hFin x0 hx0
  have hmD : m ∈ D := by
    by_contra hmD
    have := hmmin x0 hx0K
    rw [hFout m hmD, hFx0] at this
    exact EReal.coe_ne_top _ (top_le_iff.1 this)
  refine ⟨m, hmD, fun z hz => ?_⟩
  have key : F m ≤ F z := by
    by_cases hzK : z ∈ Metric.closedBall v R
    · exact hmmin z hzK
    · have hR : R < ‖z - v‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hzK
        exact hzK
      calc F m ≤ F x0 := hmmin x0 hx0K
        _ ≤ F z := by
          rw [hFx0, hFin z hz]
          exact EReal.coe_le_coe_iff.2 (hcoer z hz hR)
  rw [hFin m hmD, hFin z hz] at key
  exact EReal.coe_le_coe_iff.1 key

/-- The final algebraic estimate. -/
theorem aux_cgs_alg {n : ℕ} (x xs p gx gs : EuclideanSpace ℝ (Fin n)) (L : ℝ) (_hL : 0 ≤ L)
    (hlip : ‖gx - gs‖ ≤ L * ‖x - xs‖)
    (hfirm : ‖p - xs‖ ^ 2 ≤ ⟪(x - gx) - (xs - gs), p - xs⟫) :
    ‖x - p‖ ≤ (L + 1) * ‖x - xs‖ := by
  obtain ⟨d, hd⟩ : ∃ d, d = x - xs := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = gx - gs := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = p - xs := ⟨_, rfl⟩
  have ha : (x - gx) - (xs - gs) = d - e := by rw [hd, he]; abel
  rw [ha, ← hr] at hfirm
  rw [← he, ← hd] at hlip
  have hball : ‖r - (1/2:ℝ) • (d - e)‖ ≤ (1/2) * ‖d - e‖ := by
    have hsq : ‖r - (1/2:ℝ) • (d - e)‖ ^ 2 ≤ ((1/2) * ‖d - e‖) ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, mul_pow, mul_pow,
        Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      rw [real_inner_comm] at hfirm
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have hx : x - p = (1/2:ℝ) • (d + e) - (r - (1/2:ℝ) • (d - e)) := by
    rw [hd, he, hr]; module
  rw [hx, ← hd]
  calc ‖(1/2:ℝ) • (d + e) - (r - (1/2:ℝ) • (d - e))‖
      ≤ ‖(1/2:ℝ) • (d + e)‖ + ‖r - (1/2:ℝ) • (d - e)‖ := norm_sub_le _ _
    _ ≤ (1/2) * (‖d‖ + ‖e‖) + (1/2) * (‖d‖ + ‖e‖) := by
        gcongr
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
          gcongr
          exact norm_add_le _ _
        · exact hball.trans (by gcongr; exact norm_sub_le _ _)
    _ = ‖d‖ + ‖e‖ := by ring
    _ ≤ (L + 1) * ‖d‖ := by linarith

end ProxNewton.Inexact

open ProxNewton.Inexact

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (L1 : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hg : ContDiff ℝ 1 g) (hgconv : ConvexOn ℝ Set.univ g) (hL1 : 0 ≤ L1)
    (hlip : ∀ x y, ‖gradient g x - gradient g y‖ ≤ L1 * ‖x - y‖)
    (hh : IsProperClosedConvex D h) (hxstar : IsMinimizer g D h xstar)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖compGradStep g D h 1 x‖ ≤ (L1 + 1) * ‖x - xstar‖ := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hfoc := aux_cgs_foc hgd hh.2.1 hh.2.2.1 hxstar
  have hfix := aux_cgs_fixed hgd hh.2.1 hh.2.2.1 hxstar
  have hex : ∃ p, IsProxPoint D h (x - gradient g x) p :=
    aux_cgs_exists hh hxstar.1 (w := -gradient g xstar)
      (fun y hy => by have := hfoc y hy; rw [inner_neg_left]; linarith) _
  have hp : IsProxPoint D h (x - gradient g x) (prox D h (x - gradient g x)) :=
    Classical.epsilon_spec hex
  unfold compGradStep
  have e1 : (fun y => (1:ℝ) * h y) = h := by funext y; ring
  rw [e1, inv_one, one_smul, one_smul]
  have hfirm := aux_cgs_firm hh.2.1 hh.2.2.1 hp hfix
  exact aux_cgs_alg x xstar _ _ _ L1 hL1 (hlip x xstar) hfirm
