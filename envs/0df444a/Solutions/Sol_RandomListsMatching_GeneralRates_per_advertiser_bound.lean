-- Prove2me | solution 1 for RandomListsMatching.GeneralRates.per_advertiser_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T22:35:55.288802+00:00
-- url     : https://prove2.me/submissions/178305da-39cc-4240-907f-c94d45938c05

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

set_option autoImplicit false

open RandomListsMatching.GeneralRates



lemma cd_h_zero (y : ℝ) : h y 0 = 1 - Real.exp (-y) := by
  unfold h
  split_ifs with hy
  · subst hy; simp
  · have : y ≠ 0 := fun e => hy e.symm
    field_simp
    simp

lemma cd_g_integral (y x : ℝ) :
    g y x = ∫ θ in (0:ℝ)..1, y * Real.exp (-(y*θ)) * (1 - Real.exp (-(x*(1-θ)))) := by
  have hh0 := cd_h_zero y
  have hcomb : ∀ θ : ℝ, Real.exp (-(y*θ)) * Real.exp (-(x*(1-θ)))
      = Real.exp (-x) * Real.exp (-((y-x)*θ)) := by
    intro θ; rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  by_cases hxy : x = y
  · subst hxy
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ => -Real.exp (-(x*θ)) - x * Real.exp (-x) * θ)]
    · rw [show g x x = h x 0 - h x x from rfl, hh0]
      unfold h; rw [if_pos rfl]; simp; ring
    · intro θ _
      have h1 : HasDerivAt (fun θ : ℝ => -(x*θ)) (-x) θ := by
        exact ((hasDerivAt_id' θ).const_mul x).neg.congr_deriv (by ring)
      have h2 := h1.exp
      have h3 := (hasDerivAt_id' θ).const_mul (x * Real.exp (-x))
      refine (h2.neg.sub h3).congr_deriv ?_
      have := hcomb θ
      simp only [sub_self, zero_mul, neg_zero, Real.exp_zero, mul_one] at this
      linear_combination x * this
    · apply Continuous.intervalIntegrable; fun_prop
  · have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ => -Real.exp (-(y*θ)) + y / (y - x) * (Real.exp (-x) * Real.exp (-((y-x)*θ))))]
    · rw [show g y x = h y 0 - h y x from rfl, hh0]
      unfold h
      rw [if_neg hxy]
      simp only [mul_one, mul_zero, neg_zero, Real.exp_zero, sub_zero]
      have e1 : Real.exp (-x) * Real.exp (-(y - x)) = Real.exp (-y) := by
        rw [← Real.exp_add]; ring_nf
      rw [e1]; field_simp; ring
    · intro θ _
      have h1 : HasDerivAt (fun θ : ℝ => -(y*θ)) (-y) θ := by
        exact ((hasDerivAt_id' θ).const_mul y).neg.congr_deriv (by ring)
      have h4 : HasDerivAt (fun θ : ℝ => -((y-x)*θ)) (-(y-x)) θ := by
        exact ((hasDerivAt_id' θ).const_mul (y-x)).neg.congr_deriv (by ring)
      have h5 := ((h4.exp).const_mul (Real.exp (-x))).const_mul (y / (y - x))
      refine ((h1.exp.neg).add h5).congr_deriv ?_
      have e2 : y / (y - x) * (Real.exp (-x) * (Real.exp (-((y - x) * θ)) * -(y - x)))
          = -(y * (Real.exp (-x) * Real.exp (-((y - x) * θ)))) := by field_simp
      rw [e2]
      linear_combination y * hcomb θ
    · apply Continuous.intervalIntegrable; fun_prop

lemma cd_int_one_sub_mul_exp : ∫ θ in (0:ℝ)..1, (1 - θ) * Real.exp (-θ) = Real.exp (-1) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => θ * Real.exp (-θ))]
  · simp
  · intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => -θ) (-1) θ := (hasDerivAt_id' θ).neg
    refine ((hasDerivAt_id' θ).mul h1.exp).congr_deriv ?_
    ring
  · apply Continuous.intervalIntegrable; fun_prop





lemma cd_F_nonneg {x θ : ℝ} (hx : 0 ≤ x) (hθ : θ ≤ 1) : 0 ≤ 1 - Real.exp (-(x*(1-θ))) := by
  have : 0 ≤ x*(1-θ) := mul_nonneg hx (by linarith)
  have : Real.exp (-(x*(1-θ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma cd_F_le_lin (x θ : ℝ) : 1 - Real.exp (-(x*(1-θ))) ≤ x*(1-θ) := by
  have := Real.add_one_le_exp (-(x*(1-θ)))
  linarith

lemma cd_F_le_one (x θ : ℝ) : 1 - Real.exp (-(x*(1-θ))) ≤ 1 := by
  have := Real.exp_pos (-(x*(1-θ))); linarith

lemma cd_w_le {y θ : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    y * Real.exp (-(y*θ)) ≤ 1 * Real.exp (-(1*θ)) := by
  have e : Real.exp (-(1*θ)) = Real.exp (-(y*θ)) * Real.exp (-((1-y)*θ)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : y ≤ Real.exp (-((1-y)*θ)) := by
    have := Real.add_one_le_exp (-((1-y)*θ))
    nlinarith
  rw [e, one_mul, mul_comm y]
  exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

lemma cd_w_diff_le {f θ : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hθ0 : 0 ≤ θ) :
    1 * Real.exp (-(1*θ)) - f * Real.exp (-(f*θ)) ≤ 1 - f := by
  have h1 : Real.exp (-(1*θ)) ≤ Real.exp (-(f*θ)) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (-(f*θ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  nlinarith

lemma cd_g_nonneg {y x : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) : 0 ≤ g y x := by
  rw [cd_g_integral]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro θ hθ
  exact mul_nonneg (mul_nonneg hy (Real.exp_pos _).le) (cd_F_nonneg hx hθ.2)

lemma cd_g_le_one {y x : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hx : 0 ≤ x) : g y x ≤ g 1 x := by
  rw [cd_g_integral, cd_g_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro θ hθ
  exact mul_le_mul_of_nonneg_right (cd_w_le hy0 hy1 hθ.1 hθ.2) (cd_F_nonneg hx hθ.2)

lemma cd_g_le_lin {f x : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hx : 0 ≤ x) :
    g f x ≤ x * Real.exp (-1) := by
  calc g f x ≤ g 1 x := cd_g_le_one hf0 hf1 hx
    _ ≤ ∫ θ in (0:ℝ)..1, x * ((1 - θ) * Real.exp (-θ)) := by
        rw [cd_g_integral]
        apply intervalIntegral.integral_mono_on (by norm_num)
        · apply Continuous.intervalIntegrable; fun_prop
        · apply Continuous.intervalIntegrable; fun_prop
        intro θ hθ
        have := cd_F_le_lin x θ
        have he := Real.exp_pos (-θ)
        simp only [one_mul]
        nlinarith
    _ = x * Real.exp (-1) := by
        rw [intervalIntegral.integral_const_mul, cd_int_one_sub_mul_exp]

lemma cd_int_lin : ∫ θ in (0:ℝ)..1, (1 - θ) = 1/2 := by
  rw [intervalIntegral.integral_sub (by simp) (by simp)]
  simp; norm_num

lemma cd_g_diff {f x : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hx : 0 ≤ x) :
    g 1 x - g f x ≤ (1 - f) * x / 2 := by
  rw [cd_g_integral, cd_g_integral, ← intervalIntegral.integral_sub]
  · calc _ ≤ ∫ θ in (0:ℝ)..1, ((1 - f) * x) * (1 - θ) := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · apply Continuous.intervalIntegrable; fun_prop
          · apply Continuous.intervalIntegrable; fun_prop
          intro θ hθ
          have h1 := cd_w_diff_le hf0 hf1 hθ.1
          have h2 := cd_w_le hf0 hf1 hθ.1 hθ.2
          have h3 := cd_F_le_lin x θ
          have h4 := cd_F_nonneg hx hθ.2
          have h5 : 0 ≤ x * (1 - θ) := mul_nonneg hx (by linarith [hθ.2])
          rw [← sub_mul]
          calc _ ≤ (1 - f) * (1 - Real.exp (-(x * (1 - θ)))) :=
                mul_le_mul_of_nonneg_right h1 h4
            _ ≤ (1 - f) * (x * (1 - θ)) := mul_le_mul_of_nonneg_left h3 (by linarith)
            _ = _ := by ring
      _ = (1 - f) * x / 2 := by rw [intervalIntegral.integral_const_mul, cd_int_lin]; ring
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

lemma cd_g_le_W {f x : ℝ} (hf : 0 ≤ f) (hx : 0 ≤ x) : g f x ≤ 1 - Real.exp (-f) := by
  have hint : ∫ θ in (0:ℝ)..1, f * Real.exp (-(f*θ)) = 1 - Real.exp (-f) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => -Real.exp (-(f*θ)))]
    · simp; ring
    · intro θ _
      have h1 : HasDerivAt (fun θ : ℝ => -(f*θ)) (-f) θ :=
        ((hasDerivAt_id' θ).const_mul f).neg.congr_deriv (by ring)
      exact h1.exp.neg.congr_deriv (by ring)
    · apply Continuous.intervalIntegrable; fun_prop
  rw [cd_g_integral, ← hint]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro θ _
  have := cd_F_le_one x θ
  have := mul_nonneg hf (Real.exp_pos (-(f*θ))).le
  nlinarith

lemma cd_g_concave {f a b t : ℝ} (hf : 0 ≤ f) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * g f a + t * g f b ≤ g f ((1 - t) * a + t * b) := by
  rw [cd_g_integral, cd_g_integral, cd_g_integral, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
    intro θ _
    have hc := convexOn_exp.2 (Set.mem_univ (-(a*(1-θ)))) (Set.mem_univ (-(b*(1-θ))))
      (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    simp only [smul_eq_mul] at hc
    have e : (1 - t) * -(a * (1 - θ)) + t * -(b * (1 - θ)) = -(((1 - t) * a + t * b) * (1 - θ)) := by
      ring
    rw [e] at hc
    have hw := mul_nonneg hf (Real.exp_pos (-(f*θ))).le
    nlinarith
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

lemma cd_g_zero (f : ℝ) : g f 0 = 0 := by
  unfold g; simp

lemma cd_g_self (f : ℝ) : g f f = 1 - Real.exp (-f) - f * Real.exp (-f) := by
  have := cd_g_zero f
  unfold g at *
  unfold h; simp only [if_pos rfl]
  rw [show (if (0:ℝ) = f then f * Real.exp (-f) else f / (f - 0) * (Real.exp (-0) - Real.exp (-f)))
      = h f 0 from rfl]
  unfold h
  split_ifs with h0
  · subst h0; simp
  · have : f ≠ 0 := fun e => h0 e.symm
    field_simp; simp





lemma cd_int_w (f : ℝ) : ∫ θ in (0:ℝ)..1, f * Real.exp (-(f*θ)) = 1 - Real.exp (-f) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => -Real.exp (-(f*θ)))]
  · simp; ring
  · intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => -(f*θ)) (-f) θ :=
      ((hasDerivAt_id' θ).const_mul f).neg.congr_deriv (by ring)
    exact h1.exp.neg.congr_deriv (by ring)
  · apply Continuous.intervalIntegrable; fun_prop

lemma cd_int_lin4 (A B C D : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hD : Continuous D) (a b c : ℝ) :
    ∫ θ in (0:ℝ)..1, (A θ - a * B θ - b * C θ + c * D θ)
      = (∫ θ in (0:ℝ)..1, A θ) - a * (∫ θ in (0:ℝ)..1, B θ) - b * (∫ θ in (0:ℝ)..1, C θ)
        + c * (∫ θ in (0:ℝ)..1, D θ) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

lemma cd_sign {u v τ τ' : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ (Real.exp (-(u*τ')) - Real.exp (-(u*τ))) * (Real.exp (-(v*τ')) - Real.exp (-(v*τ))) := by
  rcases le_total τ τ' with h | h
  · have h1 : Real.exp (-(u*τ')) ≤ Real.exp (-(u*τ)) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-(v*τ')) ≤ Real.exp (-(v*τ)) := Real.exp_le_exp.mpr (by nlinarith)
    nlinarith
  · have h1 : Real.exp (-(u*τ)) ≤ Real.exp (-(u*τ')) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-(v*τ)) ≤ Real.exp (-(v*τ')) := Real.exp_le_exp.mpr (by nlinarith)
    nlinarith

lemma cd_cheb {f u v : ℝ} (hf : 0 < f) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    g f u * g f v ≤ (1 - Real.exp (-f)) * (g f u + g f v - g f (u + v)) := by
  set W := 1 - Real.exp (-f) with hW
  have hWpos : 0 < W := by
    have : Real.exp (-f) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  -- identity
  have hid : g f u + g f v - g f (u + v) = ∫ θ in (0:ℝ)..1,
      f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))) * (1 - Real.exp (-(v*(1-θ)))) := by
    rw [cd_g_integral, cd_g_integral, cd_g_integral, ← intervalIntegral.integral_add,
      ← intervalIntegral.integral_sub]
    · apply intervalIntegral.integral_congr
      intro θ _
      simp only
      have e : Real.exp (-((u + v) * (1 - θ))) = Real.exp (-(u*(1-θ))) * Real.exp (-(v*(1-θ))) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]; ring
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  rcases hv.eq_or_lt with hv0 | hv0
  · subst hv0
    have : g f 0 = 0 := by unfold g; simp
    rw [this]; simp
  -- crossing point
  have hgv0 : 0 ≤ g f v := by
    rw [cd_g_integral]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro θ hθ
    have : Real.exp (-(v*(1-θ))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hθ.2])
    have := mul_nonneg hf.le (Real.exp_pos (-(f*θ))).le
    nlinarith
  have hgv1 : g f v ≤ W * (1 - Real.exp (-v)) := by
    rw [cd_g_integral, hW, ← cd_int_w, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
    intro θ hθ
    have : Real.exp (-v) ≤ Real.exp (-(v*(1-θ))) := Real.exp_le_exp.mpr (by nlinarith [hθ.1])
    have := mul_nonneg hf.le (Real.exp_pos (-(f*θ))).le
    nlinarith
  set d := g f v / W with hd
  have hd0 : 0 ≤ d := div_nonneg hgv0 hWpos.le
  have hd1 : d ≤ 1 - Real.exp (-v) := by rw [hd, div_le_iff₀ hWpos]; linarith
  have h1d : 0 < 1 - d := by have := Real.exp_pos (-v); linarith
  set τs := -Real.log (1 - d) / v with hτs
  have hexp_v : Real.exp (-(v*τs)) = 1 - d := by
    rw [hτs, show -(v * (-Real.log (1 - d) / v)) = Real.log (1 - d) by field_simp]
    exact Real.exp_log h1d
  set p := 1 - Real.exp (-(u*τs)) with hp
  have hnonneg : 0 ≤ ∫ θ in (0:ℝ)..1,
      (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))) * (1 - Real.exp (-(v*(1-θ))))
        - d * (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))))
        - p * (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(v*(1-θ)))))
        + (p * d) * (f * Real.exp (-(f*θ)))) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro θ _
    have hs := cd_sign (τ := 1 - θ) (τ' := τs) hu hv
    rw [hexp_v] at hs
    have hw := mul_nonneg hf.le (Real.exp_pos (-(f*θ))).le
    have : (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))) * (1 - Real.exp (-(v*(1-θ))))
        - d * (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(u*(1-θ)))))
        - p * (f * Real.exp (-(f*θ)) * (1 - Real.exp (-(v*(1-θ)))))
        + (p * d) * (f * Real.exp (-(f*θ))))
        = (f * Real.exp (-(f*θ))) * ((Real.exp (-(u * τs)) - Real.exp (-(u * (1 - θ)))) *
          (1 - d - Real.exp (-(v * (1 - θ))))) := by rw [hp]; ring
    rw [this]; exact mul_nonneg hw hs
  rw [cd_int_lin4 _ _ _ _ (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop),
    ← cd_g_integral, ← cd_g_integral, cd_int_w, ← hid] at hnonneg
  have hgvd : g f v = d * W := by rw [hd]; field_simp
  rw [hgvd] at hnonneg ⊢
  have hgu0 : 0 ≤ g f u := by
    rw [cd_g_integral]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro θ hθ
    have : Real.exp (-(u*(1-θ))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hθ.2])
    have := mul_nonneg hf.le (Real.exp_pos (-(f*θ))).le
    nlinarith
  nlinarith



lemma cd_exp_up4 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp t ≤ 1 + t + t^2/2 + t^3/6 + t^4*(5/96) := by
  have h := Real.exp_bound (x := t) (by rw [abs_of_nonneg ht0]; exact ht1) (n := 4) (by norm_num)
  rw [abs_of_nonneg ht0] at h
  simp [Finset.sum_range_succ, Nat.factorial] at h
  have := (abs_le.mp h).2
  norm_num at this
  linarith

lemma cd_exp_neg_up6 {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    Real.exp (-f) ≤ 1 - f + f^2/2 - f^3/6 + f^4/24 - f^5/120 + f^6*(7/4320) := by
  have h := Real.exp_bound (x := -f) (by rw [abs_neg, abs_of_nonneg hf0]; exact hf1) (n := 6)
    (by norm_num)
  rw [abs_neg, abs_of_nonneg hf0] at h
  simp [Finset.sum_range_succ, Nat.factorial] at h
  have := (abs_le.mp h).2
  norm_num at this
  nlinarith

lemma cd_E2_c0 (ε L : ℝ) (hε1 : 0.3678794411 < ε) (hε2 : ε < 0.3678794416)
    (hL1 : 0.6931471803 < L) (hL2 : L < 0.6931471808) :
    (8.2e-5:ℝ) ≤ 0.294 - 0.294*L - ε/2 + L*ε^2 := by
  have h1 : (0.3678794411:ℝ)^2 ≤ ε^2 := pow_le_pow_left₀ (by norm_num) hε1.le 2
  have h2 : 0.6931471803 * (0.3678794411:ℝ)^2 ≤ L * ε^2 :=
    mul_le_mul hL1.le h1 (by positivity) (by linarith)
  norm_num at h2 ⊢
  linarith

lemma cd_E2_cs (ε L : ℝ) (ha0 : 0.3678 ≤ ε) (ha1 : ε ≤ 0.3679) (hb0 : 0.6931 ≤ L) (hb1 : L ≤ 0.6932) :
    (0.05:ℝ) ≤ (1 - L)*(0.706 - ε^2*L^2/2) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε)) + -(ε*(1/2 - ε)))
    ∧ (-0.035:ℝ) ≤ -(1 - L)*ε*(L^2/8 - ε*L) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/2 + -(ε*(1/2 - ε)))
    ∧ (-0.015:ℝ) ≤ -(1 - L)*ε*(ε/2 - L/4) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/6 + -(ε*(1/2 - ε))/2)
    ∧ (-0.02:ℝ) ≤ -(1 - L)*ε/8 - (5*((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/96 + -(ε*(1/2 - ε))/6)
    ∧ (0:ℝ) ≤ -(5*(-(ε*(1/2 - ε)))/96) := by
  have e2 : ε^2 ≤ 0.3679^2 := pow_le_pow_left₀ (by linarith) ha1 2
  have e2' : 0.3678^2 ≤ ε^2 := pow_le_pow_left₀ (by norm_num) ha0 2
  have l2 : L^2 ≤ 0.6932^2 := pow_le_pow_left₀ (by linarith) hb1 2
  have hεL : ε^2*L^2 ≤ 0.3679^2*0.6932^2 := mul_le_mul e2 l2 (by positivity) (by positivity)
  have hεL1 : ε*L ≤ 0.3679*0.6932 := mul_le_mul ha1 hb1 (by linarith) (by norm_num)
  have hεL0 : 0.3678*0.6931 ≤ ε*L := mul_le_mul ha0 hb0 (by norm_num) (by linarith)
  have hεεL : ε^2*L ≤ 0.3679^2*0.6932 := mul_le_mul e2 hb1 (by linarith) (by positivity)
  have hεεL0 : 0.3678^2*0.6931 ≤ ε^2*L := mul_le_mul e2' hb0 (by norm_num) (by positivity)
  have hεLL : ε*L^2 ≤ 0.3679*0.6932^2 := mul_le_mul ha1 l2 (by positivity) (by norm_num)
  have l2' : 0.6931^2 ≤ L^2 := pow_le_pow_left₀ (by norm_num) hb0 2
  have hεLL0 : 0.3678*0.6931^2 ≤ ε*L^2 := mul_le_mul ha0 l2' (by positivity) (by linarith)
  have hεεLL : ε^2*L^2 ≥ 0.3678^2*0.6931^2 := mul_le_mul e2' l2' (by positivity) (by positivity)
  have hεLLL : ε^2*L^3 ≤ 0.3679^2*0.6932^3 := by
    have : L^3 ≤ 0.6932^3 := pow_le_pow_left₀ (by linarith) hb1 3
    exact mul_le_mul e2 this (by positivity) (by positivity)
  have hεLLL0 : ε^2*L^3 ≥ 0.3678^2*0.6931^3 := by
    have : 0.6931^3 ≤ L^3 := pow_le_pow_left₀ (by norm_num) hb0 3
    exact mul_le_mul e2' this (by positivity) (by positivity)
  have hεLLl : ε*L^3 ≤ 0.3679*0.6932^3 := by
    have : L^3 ≤ 0.6932^3 := pow_le_pow_left₀ (by linarith) hb1 3
    exact mul_le_mul ha1 this (by positivity) (by norm_num)
  have hεLLl0 : ε*L^3 ≥ 0.3678*0.6931^3 := by
    have : 0.6931^3 ≤ L^3 := pow_le_pow_left₀ (by norm_num) hb0 3
    exact mul_le_mul ha0 this (by positivity) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e : (1 - L)*(0.706 - ε^2*L^2/2) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε)) + -(ε*(1/2 - ε)))
        = 0.706 - 0.706*L - ε^2*L^2/2 + ε^2*L^3/2 - ε - ε^2 + L*ε + ε^2*L := by ring
    rw [e]; norm_num at *; nlinarith
  · have e : -(1 - L)*ε*(L^2/8 - ε*L) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/2 + -(ε*(1/2 - ε)))
        = -(ε*L^2)/8 + ε^2*L + ε*L^3/8 - ε^2*L^2 - (ε + ε^2 - L*ε - ε^2*L)/2 - ε/4 + ε^2/2 + ε/2
          - ε^2 := by ring
    rw [e]; norm_num at *; nlinarith
  · have e : -(1 - L)*ε*(ε/2 - L/4) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/6 + -(ε*(1/2 - ε))/2)
        = -ε^2/2 + ε*L/4 + ε^2*L/2 - ε*L^2/4 - (ε + ε^2 - L*ε - ε^2*L)/6 - (ε/2 - ε^2)/6
          + (ε/2 - ε^2)/2 := by ring
    rw [e]; norm_num at *; nlinarith
  · have e : -(1 - L)*ε/8 - (5*((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/96 + -(ε*(1/2 - ε))/6)
        = -ε/8 + L*ε/8 - 5*(ε + ε^2 - L*ε - ε^2*L)/96 - 5*(ε/2 - ε^2)/96 + (ε/2 - ε^2)/6 := by ring
    rw [e]; norm_num at *; nlinarith
  · nlinarith

lemma cd_E2_Q (t c0 c1 c2 c3 c4 c5 : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 0.7) (h0 : 8.2e-5 ≤ c0)
    (h1 : 0.05 ≤ c1) (h2 : -0.035 ≤ c2) (h3 : -0.015 ≤ c3) (h4 : -0.02 ≤ c4) (h5 : 0 ≤ c5) :
    0 ≤ c0 + c1*t + c2*t^2 + c3*t^3 + c4*t^4 + c5*t^5 := by
  have t2 : 0 ≤ t^2 := by positivity
  have t3 : 0 ≤ t^3 := by positivity
  have t4 : 0 ≤ t^4 := by positivity
  have t5 : 0 ≤ t^5 := by positivity
  have a2 : t^2 ≤ 0.7*t := by nlinarith
  have a3 : t^3 ≤ 0.49*t := by nlinarith
  have a4 : t^4 ≤ 0.343*t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 ht0, mul_le_mul_of_nonneg_right h2 t2,
    mul_le_mul_of_nonneg_right h3 t3, mul_le_mul_of_nonneg_right h4 t4, mul_nonneg h5 t5]

lemma cd_E2_poly (t ε L E : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ L) (hε1 : 0.3678794411 < ε)
    (hε2 : ε < 0.3678794416) (hL1 : 0.6931471803 < L) (hL2 : L < 0.6931471808)
    (hE : E ≤ 1 + t + t^2/2 + t^3/6 + t^4*(5/96)) :
    0 ≤ (1 - L) * (1 - E*ε + ε*(1 - E*ε - (t/2*ε + t^2/8)*(L - t)^2) - 0.706*(1 - t))
      - ε*(1 - t)*(E/2 - E*ε) := by
  have hK : 0 ≤ (1 - L)*(ε + ε^2) + ε*(1 - t)*(1/2 - ε) := by
    have : 0 ≤ 1 - t := by linarith
    have : 0 ≤ ε*(1 - t) := by nlinarith
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hE hK
  obtain ⟨c1, c2, c3, c4, c5⟩ := cd_E2_cs ε L (by linarith) (by linarith) (by linarith) (by linarith)
  have c0 := cd_E2_c0 ε L hε1 hε2 hL1 hL2
  have hQ := cd_E2_Q t _ _ _ _ _ _ ht0 (by linarith) (le_trans c0 (le_of_eq (by ring :
    0.294 - 0.294*L - ε/2 + L*ε^2 = (1 - L)*(0.294 + ε) - ((1 - L)*(ε + ε^2) + ε*(1/2 - ε))))) c1 c2 c3 c4 c5
  have hid : (1 - L) * (1 - E*ε + ε*(1 - E*ε - (t/2*ε + t^2/8)*(L - t)^2) - 0.706*(1 - t))
      - ε*(1 - t)*(E/2 - E*ε)
      = (1 - L)*(1 + ε - 0.706*(1 - t) - ε*(t/2*ε + t^2/8)*(L - t)^2)
        - (1 + t + t^2/2 + t^3/6 + t^4*(5/96)) * ((1 - L)*(ε + ε^2) + ε*(1 - t)*(1/2 - ε))
        + ((1 + t + t^2/2 + t^3/6 + t^4*(5/96)) - E) * ((1 - L)*(ε + ε^2) + ε*(1 - t)*(1/2 - ε)) := by
    ring
  have hid2 : (1 - L)*(1 + ε - 0.706*(1 - t) - ε*(t/2*ε + t^2/8)*(L - t)^2)
        - (1 + t + t^2/2 + t^3/6 + t^4*(5/96)) * ((1 - L)*(ε + ε^2) + ε*(1 - t)*(1/2 - ε))
      = ((1 - L)*(0.294 + ε) - ((1 - L)*(ε + ε^2) + ε*(1/2 - ε)))
        + ((1 - L)*(0.706 - ε^2*L^2/2) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε)) + -(ε*(1/2 - ε)))) * t
        + (-(1 - L)*ε*(L^2/8 - ε*L) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/2 + -(ε*(1/2 - ε)))) * t^2
        + (-(1 - L)*ε*(ε/2 - L/4) - (((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/6 + -(ε*(1/2 - ε))/2)) * t^3
        + (-(1 - L)*ε/8 - (5*((1 - L)*(ε + ε^2) + ε*(1/2 - ε))/96 + -(ε*(1/2 - ε))/6)) * t^4
        + (-(5*(-(ε*(1/2 - ε)))/96)) * t^5 := by ring
  rw [hid, hid2]
  have : 0 ≤ ((1 + t + t^2/2 + t^3/6 + t^4*(5/96)) - E) * ((1 - L)*(ε + ε^2) + ε*(1 - t)*(1/2 - ε)) :=
    mul_nonneg (by linarith) hK
  linarith


lemma cd_E1_poly (f ε X : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (ha0 : 0.3678 ≤ ε) (ha1 : ε ≤ 0.3679)
    (hX : X ≤ 1 - f + f^2/2 - f^3/6 + f^4/24 - f^5/120 + f^6*(7/4320)) :
    0 ≤ 1 - X + ε*(1 - X - f*X - f^2*((1 - f)/2*ε + ((1 - f)/2)^2/2)) - 0.706*f := by
  set U := 1 - f + f^2/2 - f^3/6 + f^4/24 - f^5/120 + f^6*(7/4320) with hU
  have hK : 0 ≤ 1 + ε + ε*f := by nlinarith
  have hmono : 1 - U + ε*(1 - U - f*U - f^2*((1 - f)/2*ε + ((1 - f)/2)^2/2)) - 0.706*f
      ≤ 1 - X + ε*(1 - X - f*X - f^2*((1 - f)/2*ε + ((1 - f)/2)^2/2)) - 0.706*f := by
    nlinarith [mul_le_mul_of_nonneg_right hX hK]
  refine le_trans ?_ hmono
  have hid : 1 - U + ε*(1 - U - f*U - f^2*((1 - f)/2*ε + ((1 - f)/2)^2/2)) - 0.706*f
      = f * (0.294 + (-1/2 + 3*ε/8 - ε^2/2)*f + (1/6 - ε/12 + ε^2/2)*f^2 - (1/24)*f^3
          + (1/120 - ε/30)*f^4 + (-7/4320 + 29*ε/4320)*f^5 + (-7*ε/4320)*f^6) := by
    rw [hU]; ring
  rw [hid]
  apply mul_nonneg hf0
  have e2 : ε^2 ≤ 0.3679^2 := pow_le_pow_left₀ (by linarith) ha1 2
  have e2' : 0.3678^2 ≤ ε^2 := pow_le_pow_left₀ (by norm_num) ha0 2
  have d2 : -0.4298 ≤ -1/2 + 3*ε/8 - ε^2/2 := by nlinarith
  have d3 : 0.2036 ≤ 1/6 - ε/12 + ε^2/2 := by nlinarith
  have d5 : -0.004 ≤ 1/120 - ε/30 := by nlinarith
  have d6 : 0 ≤ -7/4320 + 29*ε/4320 := by nlinarith
  have d7 : -0.0006 ≤ -7*ε/4320 := by nlinarith
  have f2 : 0 ≤ f^2 := by positivity
  have f3 : f^3 ≤ 1 := pow_le_one₀ hf0 hf1
  have f4 : f^4 ≤ 1 := pow_le_one₀ hf0 hf1
  have f4' : 0 ≤ f^4 := by positivity
  have f5 : 0 ≤ f^5 := by positivity
  have f6 : f^6 ≤ 1 := pow_le_one₀ hf0 hf1
  have f6' : 0 ≤ f^6 := by positivity
  have q : 0 ≤ (1 - f)*(1.1 - f) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right d2 hf0, mul_le_mul_of_nonneg_right d3 f2,
    mul_le_mul_of_nonneg_right d5 f4', mul_nonneg d6 f5, mul_le_mul_of_nonneg_right d7 f6']

lemma cd_E3 {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 0.31) : 0.706 * f ≤ 1 - Real.exp (-f) := by
  have h := cd_exp_neg_up6 hf0 (by linarith)
  have f2 : 0 ≤ f^2 := by positivity
  have f4 : 0 ≤ f^4 := by positivity
  have f6 : 0 ≤ f^6 := by positivity
  have a3 : f^3 ≥ 0 := by positivity
  have a4 : f^4 ≤ f^3 := by nlinarith
  have a5 : f^5 ≥ 0 := by positivity
  have a6 : f^6 ≤ f^5 := by nlinarith [pow_le_one₀ hf0 (by linarith : f ≤ 1) (n := 1)]
  nlinarith

lemma cd_F6 {f : ℝ} (hf : 0 < f) (hf1 : f ≤ 1) {k : ℕ} (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j)
    (T : Finset (Fin k)) (hT : ∑ j ∈ T, x j ≤ 1) :
    g f (∑ j ∈ T, x j) ≤ (∑ j ∈ T, g f (x j))
      - ((∑ j ∈ T, g f (x j))^2 - ∑ j ∈ T, (g f (x j))^2) / 2 := by
  induction T using Finset.induction_on with
  | empty => simp [cd_g_zero]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha] at hT
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    set S := ∑ j ∈ T, x j with hS
    set A := ∑ j ∈ T, g f (x j) with hA
    set Q := ∑ j ∈ T, (g f (x j))^2 with hQ
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => hx j)
    have hS1 : S ≤ 1 := by linarith [hx a]
    have ih' := ih hS1
    set M := A - (A^2 - Q)/2 with hM
    set W := 1 - Real.exp (-f) with hW
    have hWpos : 0 < W := by
      have : Real.exp (-f) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hch := cd_cheb hf hS0 (hx a)
    rw [add_comm S (x a)] at hch
    have hv0 : 0 ≤ g f (x a) := cd_g_nonneg hf.le (hx a)
    have hvW : g f (x a) ≤ W := cd_g_le_W hf.le (hx a)
    have hA0 : 0 ≤ A := Finset.sum_nonneg (fun j _ => cd_g_nonneg hf.le (hx j))
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hAle : A ≤ S * Real.exp (-1) := by
      rw [hA, hS, Finset.sum_mul]
      exact Finset.sum_le_sum (fun j _ => cd_g_le_lin hf.le hf1 (hx j))
    have hε : Real.exp (-1) ≤ Real.exp (-f) := Real.exp_le_exp.mpr (by linarith)
    have hMW : W * A ≤ M := by
      have : A ≤ 2 * Real.exp (-f) := by nlinarith [Real.exp_pos (-1)]
      rw [hM, hW]; nlinarith
    have h1 : g f S * (W - g f (x a)) ≤ M * (W - g f (x a)) :=
      mul_le_mul_of_nonneg_right ih' (by linarith)
    have h2 : 0 ≤ g f (x a) * (M - W * A) := mul_nonneg hv0 (by linarith)
    have key : W * g f (x a + S) ≤ W * ((g f (x a) + A) - ((g f (x a) + A)^2 - ((g f (x a))^2 + Q))/2) := by
      nlinarith
    exact le_of_mul_le_mul_left key hWpos

lemma cd_eps_bounds : 0.3678794411 < Real.exp (-1) ∧ Real.exp (-1) < 0.3678794416 := by
  have hprod : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have hp := Real.exp_pos (-1)
  constructor <;> nlinarith

lemma cd_g_shift (f c : ℝ) (hc : c ≠ 0) :
    g f (f - c) = 1 - Real.exp (-f) - f / c * (Real.exp (-(f - c)) - Real.exp (-f)) := by
  rw [show g f (f - c) = h f 0 - h f (f - c) from rfl, cd_h_zero]
  unfold h
  rw [if_neg (by intro e; apply hc; linarith)]
  rw [show f - (f - c) = c by ring]

lemma cd_main_lower (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) {k : ℕ} (x y : Fin k → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hxy : ∀ j, x j ≤ y j) (hy : ∀ j, y j ≤ 1) (hs : ∑ j, x j ≤ f) :
    1 - Real.exp (-f) + Real.exp (-1) * (g f (∑ j, x j) - (∑ j, x j)^2 *
      ((1 - f)/2 * Real.exp (-1) + ((1 - f)/2)^2/2)) ≤ bracket f x y := by
  unfold bracket
  set s := ∑ j, x j with hsdef
  set ε := Real.exp (-1) with hεdef
  set A := ∑ j, g f (x j) with hAdef
  set Q := ∑ j, (g f (x j))^2 with hQdef
  set B := ∑ j, g 1 (x j) with hBdef
  set Bp := ∑ j, g (y j) (x j) with hBpdef
  have e1 : 1 / Real.exp 1 = ε := by rw [hεdef, Real.exp_neg]; ring
  have e2 : 1 / (2 * Real.exp 1) = ε / 2 := by rw [← e1]; field_simp
  rw [e1, e2]
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun j _ => hx j)
  have hy0 : ∀ j, 0 ≤ y j := fun j => le_trans (hx j) (hxy j)
  have hBp0 : 0 ≤ Bp := Finset.sum_nonneg (fun j _ => cd_g_nonneg (hy0 j) (hx j))
  have hBpB : Bp ≤ B := Finset.sum_le_sum (fun j _ => cd_g_le_one (hy0 j) (hy j) (hx j))
  have hAB : A ≤ B := Finset.sum_le_sum (fun j _ => cd_g_le_one hf.le hf1 (hx j))
  have hBA : B - A ≤ (1 - f)/2 * s := by
    rw [hBdef, hAdef, hsdef, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => by have := cd_g_diff hf.le hf1 (hx j); linarith)
  have hA : A ≤ s * ε := by
    rw [hAdef, hsdef, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => cd_g_le_lin hf.le hf1 (hx j))
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun j _ => cd_g_nonneg hf.le (hx j))
  have hF6 := cd_F6 hf hf1 x hx Finset.univ (by linarith)
  rw [← hsdef, ← hAdef, ← hQdef] at hF6
  have hsq : Bp^2 ≤ B^2 := pow_le_pow_left₀ hBp0 hBpB 2
  set Δ := B - A with hΔ
  have hΔ0 : 0 ≤ Δ := by linarith
  have hα : 0 ≤ (1 - f)/2 * s := mul_nonneg (by linarith) hs0
  have hAD : A * Δ ≤ (s * ε) * ((1 - f)/2 * s) := mul_le_mul hA hBA hΔ0 (by positivity)
  have hDD : Δ^2 ≤ ((1 - f)/2 * s)^2 := pow_le_pow_left₀ hΔ0 hBA 2
  have hB : B = A + Δ := by rw [hΔ]; ring
  have key : g f s - s^2 * ((1 - f)/2 * ε + ((1 - f)/2)^2/2) ≤ A + Q/2 - Bp^2/2 := by
    rw [hB] at hsq
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hε0]

lemma cd_concave_ends {f a b s : ℝ} (hf : 0 ≤ f) (hab : a < b) (has : a ≤ s) (hsb : s ≤ b)
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 ≤ ε)
    (ha : 0 ≤ 1 - Real.exp (-f) + ε * (g f a - a^2 * C) - 0.706 * f)
    (hb : 0 ≤ 1 - Real.exp (-f) + ε * (g f b - b^2 * C) - 0.706 * f) :
    0 ≤ 1 - Real.exp (-f) + ε * (g f s - s^2 * C) - 0.706 * f := by
  set t := (s - a) / (b - a) with ht
  have hba : 0 < b - a := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hba.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hba]; linarith
  have hs : s = (1 - t) * a + t * b := by rw [ht]; field_simp; ring
  have hcv := cd_g_concave (f := f) (a := a) (b := b) hf ht0 ht1
  rw [← hs] at hcv
  have hsq : 0 ≤ (1 - t) * a^2 + t * b^2 - s^2 := by
    rw [hs]; nlinarith [mul_nonneg ht0 (by linarith : (0:ℝ) ≤ 1 - t), sq_nonneg (a - b)]
  have hid : 1 - Real.exp (-f) + ε * (g f s - s^2 * C) - 0.706 * f
      = (1 - t) * (1 - Real.exp (-f) + ε * (g f a - a^2 * C) - 0.706 * f)
        + t * (1 - Real.exp (-f) + ε * (g f b - b^2 * C) - 0.706 * f)
        + ε * (g f s - ((1 - t) * g f a + t * g f b))
        + ε * C * ((1 - t) * a^2 + t * b^2 - s^2) := by ring
  rw [hid]
  have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) ha
  have := mul_nonneg ht0 hb
  have := mul_nonneg hε (by linarith : (0:ℝ) ≤ g f s - ((1 - t) * g f a + t * g f b))
  have := mul_nonneg (mul_nonneg hε hC) hsq
  linarith

lemma cd_final_L (f s : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) (hs0 : 0 ≤ s) (hsf : s ≤ f)
    (hgap : f - s ≤ 1 - Real.log 2) :
    0 ≤ 1 - Real.exp (-f) + Real.exp (-1) * (g f s - s^2 *
      ((1 - f)/2 * Real.exp (-1) + ((1 - f)/2)^2/2)) - 0.706 * f := by
  set ε := Real.exp (-1) with hεdef
  obtain ⟨hε1, hε2⟩ := cd_eps_bounds
  rw [← hεdef] at hε1 hε2
  have hε0 : 0 ≤ ε := by linarith
  have hC : 0 ≤ (1 - f)/2 * ε + ((1 - f)/2)^2/2 := by
    have : 0 ≤ (1 - f)/2 * ε := mul_nonneg (by linarith) hε0
    positivity
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  -- endpoint b = f
  have hEb : 0 ≤ 1 - Real.exp (-f) + ε * (g f f - f^2 *
      ((1 - f)/2 * ε + ((1 - f)/2)^2/2)) - 0.706 * f := by
    rw [cd_g_self]
    have := cd_E1_poly f ε (Real.exp (-f)) hf.le hf1 (by linarith) (by linarith)
      (cd_exp_neg_up6 hf.le hf1)
    linarith
  by_cases hcase : f ≤ 1 - Real.log 2
  · -- a = 0
    rcases hs0.eq_or_lt with h0 | h0
    · rw [← h0, cd_g_zero]
      have := cd_E3 hf.le (by linarith)
      nlinarith
    have ha0 : 0 ≤ 1 - Real.exp (-f) + ε * (g f 0 - 0^2 *
        ((1 - f)/2 * ε + ((1 - f)/2)^2/2)) - 0.706 * f := by
      rw [cd_g_zero]
      have := cd_E3 hf.le (by linarith)
      nlinarith
    exact cd_concave_ends hf.le hf h0.le hsf _ hC ε hε0 ha0 hEb
  · have hcase' : 1 - Real.log 2 < f := lt_of_not_ge hcase
    set L := Real.log 2 with hLdef
    have hcpos : 0 < 1 - L := by linarith
    have hEa : 0 ≤ 1 - Real.exp (-f) + ε * (g f (f - (1 - L)) - (f - (1 - L))^2 *
        ((1 - f)/2 * ε + ((1 - f)/2)^2/2)) - 0.706 * f := by
      rw [cd_g_shift f (1 - L) hcpos.ne']
      obtain ⟨t, rfl⟩ : ∃ t, f = 1 - t := ⟨1 - f, by ring⟩
      have ht0 : 0 ≤ t := by linarith
      have htL : t ≤ L := by linarith
      have hexpf : Real.exp (-(1 - t)) = Real.exp t * ε := by
        rw [hεdef, ← Real.exp_add]; congr 1; ring
      have hexpa : Real.exp (-(1 - t - (1 - L))) = Real.exp t / 2 := by
        rw [show -(1 - t - (1 - L)) = t - L by ring, Real.exp_sub, hLdef,
          Real.exp_log (by norm_num)]
      rw [hexpf, hexpa, show 1 - t - (1 - L) = L - t by ring]
      have hP := cd_E2_poly t ε L (Real.exp t) ht0 htL hε1 hε2 hL1 hL2
        (cd_exp_up4 ht0 (by linarith))
      refine (mul_nonneg_iff_of_pos_left hcpos).mp ?_
      refine le_of_le_of_eq hP ?_
      have hinv : (1 - L)⁻¹ * (1 - L) = 1 := inv_mul_cancel₀ hcpos.ne'
      linear_combination (ε * (1 - t) * (Real.exp t / 2 - Real.exp t * ε)) * hinv
    exact cd_concave_ends hf.le (by linarith) (by linarith) hsf _ hC ε hε0 hEa hEb

open RandomListsMatching.GeneralRates in
theorem solution (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) {k : ℕ} (x y : Fin k → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hxy : ∀ j, x j ≤ y j) (hy : ∀ j, y j ≤ 1) (hs : ∑ j, x j ≤ f)
    (hgap : f - ∑ j, x j ≤ 1 - Real.log 2) :
    (0.706 : ℝ) ≤ bracket f x y / f := by
  have h1 := cd_main_lower f hf hf1 x y hx hxy hy hs
  have h2 := cd_final_L f (∑ j, x j) hf hf1 (Finset.sum_nonneg (fun j _ => hx j)) hs hgap
  rw [le_div_iff₀ hf]
  linarith
