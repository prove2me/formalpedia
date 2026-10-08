-- Prove2me | solution 1 for OnlineConvexOpt.SecondOrder.online_newton_step_regret_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:42:51.690417+00:00
-- url     : https://prove2.me/submissions/6c13c78f-1023-4d5e-887b-a21143ed78b8

import Mathlib
import Definitions.Def_OnlineConvexOpt_SecondOrder_ExpConcave
import Definitions.Def_OnlineConvexOpt_SecondOrder_OnlineNewtonStep
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open OnlineConvexOpt.SecondOrder OnlineConvexOpt.FirstOrder


namespace OnlineConvexOpt.SecondOrder

theorem onsv2_scalar (z : ℝ) (h1 : -1 ≤ z) (h2 : z ≤ 1) :
    1 - z ≤ Real.exp (-z - z ^ 2 / 4) := by
  rcases le_or_gt z 0 with hz | hz
  · have hw : 0 ≤ -z - z ^ 2 / 4 := by nlinarith
    have := Real.quadratic_le_exp_of_nonneg hw
    nlinarith [sq_nonneg z, sq_nonneg (z ^ 2), mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ z + 1)]
  · -- ψ(z) = (1 - z) * exp(z + z^2/4) is antitone on [0,1]
    set ψ : ℝ → ℝ := fun z => (1 - z) * Real.exp (z + z ^ 2 / 4) with hψ
    have hd : ∀ u, HasDerivAt ψ (-(u / 2 + u ^ 2 / 2) * Real.exp (u + u ^ 2 / 4)) u := by
      intro u
      have e1 : HasDerivAt (fun u : ℝ => u + u ^ 2 / 4) (1 + 2 * u / 4) u := by
        have := (hasDerivAt_id u).add ((hasDerivAt_pow 2 u).div_const 4)
        exact this.congr_deriv (by simp)
      have := ((hasDerivAt_id u).const_sub 1).mul e1.exp
      exact this.congr_deriv (by simp; ring)
    have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      · exact fun u _ => (hd u).continuousAt.continuousWithinAt
      · exact fun u _ => (hd u).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        rw [(hd u).deriv]
        have : 0 ≤ u / 2 + u ^ 2 / 2 := by nlinarith [hu.1]
        have := Real.exp_pos (u + u ^ 2 / 4)
        nlinarith
    have := hanti ⟨le_rfl, zero_le_one⟩ ⟨hz.le, h2⟩ hz.le
    simp only [hψ] at this
    norm_num at this
    have he : Real.exp (-z - z ^ 2 / 4) * Real.exp (z + z ^ 2 / 4) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have hp := Real.exp_pos (z + z ^ 2 / 4)
    nlinarith [Real.exp_pos (-z - z ^ 2 / 4)]

theorem onsv2_first_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {h : E → ℝ} (hK : ConcaveOn ℝ K h) {y p : E} (hy : y ∈ K) (hp : p ∈ K)
    {L : E →L[ℝ] ℝ} (hL : HasFDerivAt h L y) : h p ≤ h y + L (p - y) := by
  have hpath : HasDerivAt (fun s : ℝ => y + s • (p - y)) ((1:ℝ) • (p - y)) 0 :=
    ((hasDerivAt_id (0:ℝ)).smul_const (p - y)).const_add y
  have hL' : HasFDerivAt h L (y + (0:ℝ) • (p - y)) := by simpa using hL
  have hφ := hL'.comp_hasDerivAt (0:ℝ) hpath
  have ht := hφ.tendsto_slope_zero_right
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      h p - h y ≤ t⁻¹ • ((h ∘ fun s : ℝ => y + s • (p - y)) (0 + t) -
        (h ∘ fun s : ℝ => y + s • (p - y)) 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    have hc := hK.2 hy hp (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1.le (by ring)
    have heq : (1 - t) • y + t • p = y + t • (p - y) := by
      simp [sub_smul, smul_sub]; abel
    rw [heq] at hc
    simp only [Function.comp, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht.1]
    simp only [smul_eq_mul] at hc
    linarith
  have := ge_of_tendsto ht hev
  simp at this
  rw [map_sub]; linarith

theorem onsv2_quad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {K : Set E} {f : E → ℝ} {α β G D : ℝ} (hf : IsExpConcaveOn α K f) (hα : 0 < α)
    (hβ : 0 < β) (hβα : β ≤ α) (hβGD : β * (G * D) ≤ 1) {y p g : E} (hy : y ∈ K) (hp : p ∈ K)
    (hg : HasGradientAt f g y) (hgG : ‖g‖ ≤ G) (hd : ‖p - y‖ ≤ D) :
    f y + inner ℝ g (p - y) + β / 4 * (inner ℝ g (p - y)) ^ 2 ≤ f p := by
  have hKc : Convex ℝ K := hf.1.1
  set r := β / α with hr
  have hr0 : 0 ≤ r := div_nonneg hβ.le hα.le
  have hr1 : r ≤ 1 := (div_le_one hα).2 hβα
  have key : ∀ z, Real.exp (-β * f z) = (Real.exp (-α * f z)) ^ r := by
    intro z
    rw [← Real.exp_mul]; congr 1; rw [hr]; field_simp
  have hc2 : ConcaveOn ℝ K (fun z => Real.exp (-β * f z)) := by
    refine ⟨hKc, ?_⟩
    intro a ha b hb s t hs ht hst
    have h1 := hf.2.2 ha hb hs ht hst
    simp only [smul_eq_mul] at h1 ⊢
    rw [key, key, key]
    calc s * Real.exp (-α * f a) ^ r + t * Real.exp (-α * f b) ^ r
        ≤ (s * Real.exp (-α * f a) + t * Real.exp (-α * f b)) ^ r := by
          have := (Real.concaveOn_rpow hr0 hr1).2 (Set.mem_Ici.2 (Real.exp_pos (-α * f a)).le)
            (Set.mem_Ici.2 (Real.exp_pos (-α * f b)).le) hs ht hst
          simpa [smul_eq_mul] using this
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 hr0
  have hD : HasFDerivAt (fun z => Real.exp (-β * f z))
      (Real.exp (-β * f y) • (-β • (InnerProductSpace.toDual ℝ E g : E →L[ℝ] ℝ))) y :=
    (hg.hasFDerivAt.const_mul (-β)).exp
  have h1 := onsv2_first_order hc2 hy hp hD
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, InnerProductSpace.toDual_apply_apply,
    smul_eq_mul] at h1
  set a := inner ℝ g (p - y) with ha
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hgG
  have habs : |a| ≤ G * D := by
    calc |a| ≤ ‖g‖ * ‖p - y‖ := abs_real_inner_le_norm _ _
      _ ≤ G * D := mul_le_mul hgG hd (norm_nonneg _) hG0
  have hz : |β * a| ≤ 1 := by
    rw [abs_mul, abs_of_pos hβ]
    calc β * |a| ≤ β * (G * D) := mul_le_mul_of_nonneg_left habs hβ.le
      _ ≤ 1 := hβGD
  have hsc := onsv2_scalar (β * a) (abs_le.1 hz).1 (abs_le.1 hz).2
  have h2 : Real.exp (-β * f p) ≤ Real.exp (-β * f y - β * a - (β * a) ^ 2 / 4) := by
    have he : Real.exp (-β * f y - β * a - (β * a) ^ 2 / 4) =
        Real.exp (-β * f y) * Real.exp (-(β * a) - (β * a) ^ 2 / 4) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have hpos := Real.exp_pos (-β * f y)
    nlinarith
  have h3 := Real.exp_le_exp.1 h2
  have h4 : β * (f y + a + β / 4 * a ^ 2) ≤ β * f p := by nlinarith
  exact le_of_mul_le_mul_left h4 hβ

theorem onsv2_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : Convex ℝ K) (A : E →L[ℝ] E)
    (hsym : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) (hpsd : ∀ v, 0 ≤ inner ℝ v (A v))
    {y p z : E} (hP : IsGeneralizedProjection A K y p) (hz : z ∈ K) :
    quadForm A (p - z) ≤ quadForm A (y - z) := by
  obtain ⟨hp, hmin⟩ := hP
  set d := z - p
  set c := inner ℝ d (A (y - p))
  set Q := inner ℝ d (A d)
  have hQ : 0 ≤ Q := hpsd d
  have hexp : ∀ s : ℝ, quadForm A ((y - p) - s • d) =
      quadForm A (y - p) - 2 * s * c + s ^ 2 * Q := by
    intro s
    have hs := hsym (y - p) d
    have hcomm : inner ℝ (y - p) (A d) = c := by
      rw [← hs, real_inner_comm]
    generalize y - p = u at hs hcomm ⊢
    unfold quadForm
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real]
    rw [hcomm]
    have : inner ℝ d (A u) = c := by rw [← hcomm, ← hs, real_inner_comm]
    rw [this]
    ring
  have hineq : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ -2 * s * c + s ^ 2 * Q := by
    intro s hs0 hs1
    have hq : p + s • d ∈ K := by
      have := hK hp hz (by linarith : (0:ℝ) ≤ 1 - s) hs0 (by ring)
      convert this using 1
      simp only [d, smul_sub, sub_smul, one_smul]; abel
    have := hmin _ hq
    have e : y - (p + s • d) = (y - p) - s • d := by abel
    rw [e, hexp] at this
    linarith
  have hc : c ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have hs0 : 0 < c / (c + Q) := div_pos hcon (by linarith)
    have hs1 : c / (c + Q) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have := hineq _ hs0.le hs1
    have hsq : c / (c + Q) * Q ≤ c := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  have h1 := hexp 1
  have e : (y - p) - (1:ℝ) • d = y - z := by simp [d]
  rw [e] at h1
  have e2 : quadForm A (p - z) = Q := by
    unfold quadForm
    have : p - z = -d := by simp [d]
    rw [this, map_neg, inner_neg_left, inner_neg_right, neg_neg]
  rw [e2, h1]
  have := hpsd (y - p)
  unfold quadForm
  nlinarith

theorem onsv2_inv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) {ε : ℝ} (hε : 0 < ε) (hc : ∀ v, ε * ‖v‖ ^ 2 ≤ inner ℝ v (A v)) (w : E) :
    A (A.inverse w) = w := by
  set B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp A with hB
  have hcoer : IsCoercive B := by
    refine ⟨ε, hε, fun u => ?_⟩
    have := hc u
    simp only [hB, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [real_inner_comm]
    nlinarith
  set e := hcoer.continuousLinearEquivOfBilin
  have he : (e : E →L[ℝ] E) = A := by
    ext1 v
    apply ext_inner_right ℝ
    intro u
    simp [e, hB]
  rw [← he, ContinuousLinearMap.inverse_equiv]
  simp

theorem onsv2_ops {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ε : ℝ} (hε : 0 < ε) (g : ℕ → E) (A : ℕ → E →L[ℝ] E)
    (hA0 : A 0 = ε • (ContinuousLinearMap.id ℝ E))
    (hAup : ∀ t : ℕ, A (t + 1) = A t + InnerProductSpace.rankOne ℝ (g t) (g t)) (t : ℕ) :
    (∀ u v, inner ℝ (A t u) v = inner ℝ u (A t v)) ∧ (∀ v, ε * ‖v‖ ^ 2 ≤ inner ℝ v (A t v)) := by
  induction t with
  | zero =>
    rw [hA0]
    refine ⟨fun u v => ?_, fun v => ?_⟩
    · simp [inner_smul_left, inner_smul_right]
    · simp [inner_smul_right, real_inner_self_eq_norm_sq]
  | succ t ih =>
    rw [hAup t]
    refine ⟨fun u v => ?_, fun v => ?_⟩
    · simp only [ContinuousLinearMap.add_apply, InnerProductSpace.rankOne_apply, inner_add_left,
        inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      rw [ih.1 u v, real_inner_comm u (g t)]
      ring
    · simp only [ContinuousLinearMap.add_apply, InnerProductSpace.rankOne_apply,
        inner_add_right, inner_smul_right]
      have := ih.2 v
      rw [real_inner_comm v (g t)]
      nlinarith [sq_nonneg (inner ℝ (g t) v)]

theorem onsv2_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (α D G γ ε : ℝ) (f : ℕ → E → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → E) (A : ℕ → E →L[ℝ] E) (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) :
    RegretT K f x T ≤
      (1 / α + G * D) *
        ((∑ t ∈ Finset.range T, quadForm (A (t + 1)).inverse (g t)) + 1) := by
  obtain ⟨hx0, hA0, hgrad, hAup, hproj⟩ := hONS
  have hGD : 0 < G * D := mul_pos hGpos hDpos
  have h2γ : 2 * γ = min (1 / (G * D)) α := by rw [hγ]; ring
  have hγpos : 0 < γ := by
    have : 0 < min (1 / (G * D)) α := lt_min (by positivity) hα
    linarith
  have hβα : 2 * γ ≤ α := by rw [h2γ]; exact min_le_right _ _
  have hβGD : 2 * γ * (G * D) ≤ 1 := by
    rw [h2γ]
    calc min (1 / (G * D)) α * (G * D) ≤ 1 / (G * D) * (G * D) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hGD.le
      _ = 1 := by field_simp
  have hinvγ : 1 / (2 * γ) ≤ 1 / α + G * D := by
    rw [h2γ]
    rcases min_cases (1 / (G * D)) α with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; field_simp; have : 0 < 1 / α := by positivity
      nlinarith
    · rw [h]; have : 0 < G * D := hGD; linarith
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hKc : Convex ℝ K := (hf 0).1.1
  have hxK : ∀ t, x t ∈ K := by
    intro t; induction t with
    | zero => exact hx0
    | succ t _ => exact (hproj t).1
  have hops := onsv2_ops hεpos g A hA0 hAup
  set q : ℕ → ℝ := fun t => quadForm (A (t + 1)).inverse (g t) with hq
  have hinv : ∀ t, A (t + 1) ((A (t + 1)).inverse (g t)) = g t :=
    fun t => onsv2_inv (A (t + 1)) hεpos (hops (t + 1)).2 (g t)
  have hq0 : ∀ t, 0 ≤ q t := by
    intro t
    simp only [hq, quadForm]
    have := (hops (t + 1)).2 ((A (t + 1)).inverse (g t))
    rw [hinv t, real_inner_comm] at this
    nlinarith [sq_nonneg ‖(A (t + 1)).inverse (g t)‖]
  have hmain : ∀ z ∈ K, ∑ t ∈ Finset.range T, (f t (x t) - f t z) ≤
      (1 / (2 * γ)) * ((∑ t ∈ Finset.range T, q t) + 1) := by
    intro z hz
    set P : ℕ → ℝ := fun t => quadForm (A t) (x t - z) with hP
    have hstep : ∀ t, f t (x t) - f t z ≤ γ / 2 * (P t - P (t + 1)) + γ⁻¹ * q t / 2 := by
      intro t
      have hgG := hG t (x t) (hxK t) (g t) (hgrad t)
      have hdz : ‖z - x t‖ ≤ D := by rw [← dist_eq_norm]; exact hD z hz (x t) (hxK t)
      have hquad := onsv2_quad (hf t) hα (by linarith) hβα hβGD (hxK t) hz (hgrad t) hgG hdz
      set w := (A (t + 1)).inverse (g t) with hw
      have hsym := (hops (t + 1)).1
      have hpsd : ∀ v, 0 ≤ inner ℝ v (A (t + 1) v) := fun v => by
        have := (hops (t + 1)).2 v; nlinarith [sq_nonneg ‖v‖]
      have hpr := onsv2_proj hKc (A (t + 1)) hsym hpsd (hproj t) hz
      set u := x t - z with hu
      set a := inner ℝ (g t) u with ha
      have e1 : x t - γ⁻¹ • w - z = u - γ⁻¹ • w := by rw [hu]; abel
      have e2 : quadForm (A (t + 1)) (u - γ⁻¹ • w) =
          quadForm (A (t + 1)) u - 2 * γ⁻¹ * a + γ⁻¹ ^ 2 * q t := by
        have h1 : inner ℝ w (A (t + 1) u) = a := by
          rw [← hsym, hinv t]
        have h2 : inner ℝ u (A (t + 1) w) = a := by
          rw [hinv t, real_inner_comm]
        have h3 : inner ℝ w (A (t + 1) w) = q t := by
          simp only [hq, quadForm]; rw [← hw, hinv t, real_inner_comm]
        unfold quadForm
        simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right, RCLike.conj_to_real, h1, h2, h3]
        ring
      have e3 : quadForm (A (t + 1)) u = P t + a ^ 2 := by
        simp only [quadForm, hAup t, ContinuousLinearMap.add_apply,
          InnerProductSpace.rankOne_apply, inner_add_right, inner_smul_right]
        rw [real_inner_comm (g t) u, ← ha]
        have : P t = inner ℝ u (A t u) := rfl
        rw [this]; ring
      rw [e1, e2, e3] at hpr
      have hPt1 : P (t + 1) = quadForm (A (t + 1)) (x (t + 1) - z) := rfl
      rw [← hPt1] at hpr
      have e4 : inner ℝ (g t) (z - x t) = -a := by
        rw [ha, hu, ← inner_neg_right, neg_sub]
      rw [e4] at hquad
      have hgi : γ * γ⁻¹ = 1 := mul_inv_cancel₀ hγpos.ne'
      have k1 : γ / 2 * P (t + 1) ≤ γ / 2 * (P t + a ^ 2 - 2 * γ⁻¹ * a + γ⁻¹ ^ 2 * q t) :=
        mul_le_mul_of_nonneg_left hpr (by linarith)
      have k2 : γ / 2 * (P t + a ^ 2 - 2 * γ⁻¹ * a + γ⁻¹ ^ 2 * q t) =
          γ / 2 * P t + γ / 2 * a ^ 2 - (γ * γ⁻¹) * a + (γ * γ⁻¹) * (γ⁻¹ * q t / 2) := by ring
      rw [k2, hgi] at k1
      have : (-a) ^ 2 = a ^ 2 := by ring
      rw [this] at hquad
      nlinarith
    have hsum : ∀ N, ∑ t ∈ Finset.range N, (f t (x t) - f t z) ≤
        γ / 2 * (P 0 - P N) + γ⁻¹ * (∑ t ∈ Finset.range N, q t) / 2 := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := hstep N
        linarith
    have hPT : 0 ≤ P T := by
      have := (hops T).2 (x T - z); simp only [hP, quadForm]; nlinarith [sq_nonneg ‖x T - z‖]
    have hP0 : P 0 ≤ ε * D ^ 2 := by
      simp only [hP, quadForm, hA0, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        inner_smul_right, real_inner_self_eq_norm_sq]
      have h1 : ‖x 0 - z‖ ≤ D := by rw [← dist_eq_norm]; exact hD _ hx0 z hz
      have h2 : ‖x 0 - z‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      exact mul_le_mul_of_nonneg_left h2 hεpos.le
    have hεD : γ / 2 * (ε * D ^ 2) = 1 / (2 * γ) := by
      rw [hε]; field_simp
    have := hsum T
    have hfin : γ / 2 * (P 0 - P T) ≤ 1 / (2 * γ) := by
      rw [← hεD]; nlinarith
    have : γ⁻¹ * (∑ t ∈ Finset.range T, q t) / 2 = 1 / (2 * γ) * (∑ t ∈ Finset.range T, q t) := by
      field_simp
    nlinarith
  have hQ : 0 ≤ (∑ t ∈ Finset.range T, q t) + 1 := by
    have := Finset.sum_nonneg (fun t (_ : t ∈ Finset.range T) => hq0 t); linarith
  have hbound : ∀ z ∈ K, ∑ t ∈ Finset.range T, (f t (x t) - f t z) ≤
      (1 / α + G * D) * ((∑ t ∈ Finset.range T, q t) + 1) := fun z hz =>
    (hmain z hz).trans (mul_le_mul_of_nonneg_right hinvγ hQ)
  unfold RegretT
  have hne : ((fun y => ∑ t ∈ Finset.range T, f t y) '' K).Nonempty := ⟨_, x 0, hx0, rfl⟩
  have hle : (∑ t ∈ Finset.range T, f t (x t)) -
      (1 / α + G * D) * ((∑ t ∈ Finset.range T, q t) + 1) ≤
      sInf ((fun y => ∑ t ∈ Finset.range T, f t y) '' K) := by
    apply le_csInf hne
    rintro _ ⟨z, hz, rfl⟩
    have := hbound z hz
    rw [Finset.sum_sub_distrib] at this
    linarith
  simp only [hq] at hle
  linarith

end OnlineConvexOpt.SecondOrder

open OnlineConvexOpt.SecondOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem solution
    (K : Set E) (α D G γ ε : ℝ) (f : ℕ → E → ℝ)
    (hf : ∀ t, IsExpConcaveOn α K (f t))
    (hD : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ D)
    (hG : ∀ t, ∀ p ∈ K, ∀ v, HasGradientAt (f t) v p → ‖v‖ ≤ G)
    (hα : 0 < α) (hGpos : 0 < G) (hDpos : 0 < D)
    (hγ : γ = (1 / 2) * min (1 / (G * D)) α) (hε : ε = 1 / (γ ^ 2 * D ^ 2))
    (x g : ℕ → E) (A : ℕ → E →L[ℝ] E) (hONS : IsOnlineNewtonStep K γ ε f x g A)
    (T : ℕ) :
    RegretT K f x T ≤
      (1 / α + G * D) *
        ((∑ t ∈ Finset.range T, quadForm (A (t + 1)).inverse (g t)) + 1) := by
  exact onsv2_core K α D G γ ε f hf hD hG hα hGpos hDpos hγ hε x g A hONS T
