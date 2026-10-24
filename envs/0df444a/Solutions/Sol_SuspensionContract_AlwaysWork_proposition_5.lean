-- Prove2me | solution 1 for SuspensionContract.AlwaysWork.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T20:24:46.746311+00:00
-- url     : https://prove2.me/submissions/6c8ffd4d-3127-4f01-bbfa-d5b77c166e69

import Mathlib
import Definitions.Def_SuspensionContract_AlwaysWork_Setting
import Definitions.Def_SuspensionContract_AlwaysWork_ValueFunctions

set_option autoImplicit false

open Filter Topology

/-- Tangent-line bound for the concave power `x ↦ x ^ a`, `0 ≤ a ≤ 1`. -/
lemma sc5_tangent {a x y : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 < x) (hy : 0 < y) :
    x ^ a ≤ y * y ^ (a - 1) + a * y ^ (a - 1) * (x - y) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := a) (w₂ := 1 - a) (p₁ := x) (p₂ := y)
    ha0 (by linarith) hx.le hy.le (by ring)
  have hy1 : y ^ (1 - a) * y ^ (a - 1) = 1 := by
    rw [← Real.rpow_add hy, show (1 - a) + (a - 1) = (0 : ℝ) by ring, Real.rpow_zero]
  have hq : 0 < y ^ (a - 1) := Real.rpow_pos_of_pos hy _
  calc x ^ a = (x ^ a * y ^ (1 - a)) * y ^ (a - 1) := by rw [mul_assoc, hy1, mul_one]
    _ ≤ (a * x + (1 - a) * y) * y ^ (a - 1) := mul_le_mul_of_nonneg_right h hq.le
    _ = y * y ^ (a - 1) + a * y ^ (a - 1) * (x - y) := by ring

/-- The core inequality for `(𝒜_I V_I)(w) ≥ 0` on `(0, θ̲_K]`. -/
lemma sc5_core {μ r ρ a wbar θ w c q Q m Vb vlow : ℝ}
    (hra : r = ρ * a) (hr : 0 < r) (hρr : r < ρ) (hs : μ < ρ - r) (hμ : 0 < μ)
    (hw : 0 < w) (hwθ : w ≤ θ) (hθ : θ < wbar) (hc : 0 < c) (hq : 0 < q) (hQ : 0 < Q)
    (h36 : vlow + θ + c * (θ * Q) = Vb + m * (θ - wbar))
    (h37 : 1 + c * (a * Q) = m)
    (hm : ρ - r ≤ (ρ - r - μ) * m)
    (hB : θ * Q ≤ w * q + a * q * (θ - w)) :
    0 ≤ (μ + r) * (vlow + w + c * (w * q) - Vb)
      + (wbar - w) * (ρ * (1 + c * (a * q)) - (ρ - r)) := by
  have hρ : 0 < ρ := by linarith
  have ha0 : 0 < a := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ.le h]
  have ha1 : a < 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_le_mul_of_nonneg_left h hρ.le]
  have hk : 0 ≤ (ρ - r) * (m - 1) - μ * m := by linarith
  have hm1 : 0 < m - 1 := by
    have := mul_pos hc (mul_pos ha0 hQ); linarith
  have hθ0 : 0 < θ := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hd : 0 < a * θ + (1 - a) * w := by
    have := mul_pos ha0 hθ0; have := mul_pos h1a hw; linarith
  have heps : 0 ≤ q * (a * θ + (1 - a) * w) - θ * Q := by linarith
  have hT1 : 0 ≤ (a * θ + (1 - a) * w) * ((θ - wbar) * ((ρ - r) - (ρ - r - μ) * m)) :=
    mul_nonneg hd.le (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
  have hT2 : 0 ≤ (θ - w) * (μ * (1 - a) * (θ - w) + θ * ((ρ - r) * (m - 1) - μ * m)
      + (ρ - r) * (m - 1) * (wbar - θ)) := by
    have h1 : 0 ≤ θ - w := by linarith
    have h4 : 0 ≤ ρ - r := by linarith
    have h5 : 0 ≤ wbar - θ := by linarith
    have e1 : 0 ≤ μ * (1 - a) * (θ - w) := mul_nonneg (mul_nonneg hμ.le h1a.le) h1
    have e2 : 0 ≤ θ * ((ρ - r) * (m - 1) - μ * m) := mul_nonneg hθ0.le hk
    have e3 : 0 ≤ (ρ - r) * (m - 1) * (wbar - θ) := mul_nonneg (mul_nonneg h4 hm1.le) h5
    exact mul_nonneg h1 (by linarith)
  have hT3 : 0 ≤ c * (q * (a * θ + (1 - a) * w) - θ * Q) * (μ * w + r * wbar) := by
    have : 0 ≤ μ * w + r * wbar := by
      have := mul_pos hμ hw; have := mul_pos hr (by linarith : (0:ℝ) < wbar); linarith
    exact mul_nonneg (mul_nonneg hc.le heps) this
  have hv : vlow = Vb + m * (θ - wbar) - θ - c * (θ * Q) := by linarith
  subst hv
  subst h37
  subst hra
  have key : (a * θ + (1 - a) * w) * ((μ + ρ * a) * (Vb + (1 + c * (a * Q)) * (θ - wbar) - θ
        - c * (θ * Q) + w + c * (w * q) - Vb)
        + (wbar - w) * (ρ * (1 + c * (a * q)) - (ρ - ρ * a)))
      = (a * θ + (1 - a) * w) * ((θ - wbar) * ((ρ - ρ * a) - (ρ - ρ * a - μ) * (1 + c * (a * Q))))
        + (θ - w) * (μ * (1 - a) * (θ - w) + θ * ((ρ - ρ * a) * ((1 + c * (a * Q)) - 1)
          - μ * (1 + c * (a * Q))) + (ρ - ρ * a) * ((1 + c * (a * Q)) - 1) * (wbar - θ))
        + c * (q * (a * θ + (1 - a) * w) - θ * Q) * (μ * w + ρ * a * wbar) := by
    ring
  by_contra hneg
  push_neg at hneg
  have := mul_neg_of_pos_of_neg hd hneg
  linarith

set_option maxHeartbeats 1000000 in
open SuspensionContract.AlwaysWork in
theorem solution (P : Params) (hP : P.Standing) (h2 : P.Condition2)
    (hK : P.Klow ≤ P.K ∧ P.K < P.Kbar2) (cK mK θK : ℝ)
    (hθ : 0 < θK ∧ θK < P.wbar) (hc : 0 < cK)
    (hm : (P.ρ - P.r) / (P.ρ - P.r - P.μ) ≤ mK ∧ mK < (P.Vbar - P.vlow) / P.wbar)
    (h36 : P.Vc cK θK = P.Vbar + mK * (θK - P.wbar))
    (h37 : deriv (P.Vc cK) θK = mK)
    (h38 : P.Vc cK P.wbar = P.Vbar - P.K) :
    P.OptCond (P.VI40 cK mK θK) (P.V039 cK) := by
  obtain ⟨⟨hμl0, hμl⟩, ⟨hb, hbc⟩, hK0, ⟨hr, hrρ⟩, hA⟩ := hP
  obtain ⟨hμs, -⟩ := h2
  have hμ : 0 < P.μ := by linarith
  have hρr : P.r < P.ρ := by linarith
  have hρ : 0 < P.ρ := by linarith
  have hΔ : 0 < P.Δμ := by unfold Params.Δμ; linarith
  have hβ : 0 < P.β := div_pos hb hΔ
  have hwbar_def : P.wbar = P.β * P.μ / P.ρ := rfl
  have hwβ : P.wbar < P.β := by
    rw [hwbar_def, div_lt_iff₀ hρ]; nlinarith
  have hwpos : 0 < P.wbar := by rw [hwbar_def]; positivity
  have hVbar : P.r * P.Vbar = P.R * P.μ - P.c - (P.ρ - P.r) * P.wbar := by
    unfold Params.Vbar; field_simp
  have hvlow : P.r * P.vlow = P.μlow * P.R := by
    unfold Params.vlow; field_simp
  have hsm : 0 < P.ρ - P.r - P.μ := by linarith
  have hm' : P.ρ - P.r ≤ (P.ρ - P.r - P.μ) * mK := by
    have := hm.1; rw [div_le_iff₀ hsm] at this; linarith
  set a := P.r / P.ρ with ha
  have hra : P.r = P.ρ * a := by rw [ha]; field_simp
  have ha0 : 0 < a := div_pos hr hρ
  have ha1 : a < 1 := (div_lt_one hρ).2 hρr
  have hVc_eq : P.Vc cK = fun x => P.vlow + x + cK * x ^ a := by
    funext x; rfl
  have hVc_deriv : ∀ x, 0 < x → HasDerivAt (P.Vc cK) (1 + cK * (a * x ^ (a - 1))) x := by
    intro x hx
    rw [hVc_eq]
    have h1 := (Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).const_mul cK
    have h2 := ((hasDerivAt_id' x).const_add P.vlow).add h1
    exact h2
  have hpow : ∀ x : ℝ, 0 < x → x ^ a = x * x ^ (a - 1) := by
    intro x hx
    rw [Real.rpow_sub_one hx.ne']
    field_simp
  have hVc_val : ∀ x, 0 < x → P.Vc cK x = P.vlow + x + cK * (x * x ^ (a - 1)) := by
    intro x hx
    rw [hVc_eq]
    show P.vlow + x + cK * x ^ a = _
    rw [hpow x hx]
  have hmK : 1 + cK * (a * θK ^ (a - 1)) = mK := by
    rw [← h37, (hVc_deriv θK hθ.1).deriv]
  have hdW : ∀ (f g : ℝ → ℝ) (x g' : ℝ), HasDerivAt g g' x →
      f =ᶠ[𝓝[Set.Iic x] x] g → f x = g x → derivWithin f (Set.Iic x) x = g' :=
    fun f g x g' hg hfg hx =>
      (hg.hasDerivWithinAt.congr_of_eventuallyEq hfg hx).derivWithin (uniqueDiffWithinAt_Iic x)
  -- values of `V_I` and `V_∅`
  have hVI_lo : ∀ y, y ≤ θK → P.VI40 cK mK θK y = P.Vc cK y := by
    intro y hy; simp only [Params.VI40, if_pos hy]
  have hVI_mid : ∀ y, θK < y → y ≤ P.wbar → P.VI40 cK mK θK y = P.Vbar + mK * (y - P.wbar) := by
    intro y hy1 hy2; simp only [Params.VI40, if_neg (not_le.2 hy1), if_pos hy2]
  have hVI_hi : ∀ y, P.wbar < y → P.VI40 cK mK θK y = P.Vbar := by
    intro y hy
    simp only [Params.VI40, if_neg (not_le.2 (lt_trans hθ.2 hy)), if_neg (not_le.2 hy)]
  have hV0_lo : ∀ y, y ≤ P.wbar → P.V039 cK y = P.Vc cK y := by
    intro y hy; simp only [Params.V039, if_pos hy]
  have hV0_hi : ∀ y, P.wbar < y → P.V039 cK y = P.Vbar - P.K := by
    intro y hy; simp only [Params.V039, if_neg (not_le.2 hy)]
  have hVc0 : P.Vc cK 0 = P.vlow := by
    rw [hVc_eq]; simp only [Real.zero_rpow ha0.ne']; ring
  refine ⟨fun w hw => ⟨?_, ?_⟩, fun w hw => ?_, ?_, ?_⟩
  · -- (20) for `V_I`
    have hwβ' : P.wbar < w + P.β := by linarith
    have hVIβ := hVI_hi (w + P.β) hwβ'
    unfold Params.AI
    rcases le_or_gt w θK with hwθ | hwθ
    · have hder : derivWithin (P.VI40 cK mK θK) (Set.Iic w) w = 1 + cK * (a * w ^ (a - 1)) :=
        hdW _ _ _ _ (hVc_deriv w hw)
          (eventually_nhdsWithin_of_forall fun y hy => hVI_lo y (le_trans hy hwθ))
          (hVI_lo w hwθ)
      rw [hder, hVIβ, hVI_lo w hwθ, hVc_val w hw]
      have hB := sc5_tangent ha0.le ha1.le hθ.1 hw
      have hq : 0 < w ^ (a - 1) := Real.rpow_pos_of_pos hw _
      have hQ : 0 < θK ^ (a - 1) := Real.rpow_pos_of_pos hθ.1 _
      have h36' : P.vlow + θK + cK * (θK * θK ^ (a - 1)) = P.Vbar + mK * (θK - P.wbar) := by
        rw [← hVc_val θK hθ.1]; exact h36
      have hBw : θK * θK ^ (a - 1) ≤ w * w ^ (a - 1) + a * w ^ (a - 1) * (θK - w) := by
        rw [← hpow θK hθ.1]; exact hB
      have core := sc5_core (μ := P.μ) (Vb := P.Vbar) (wbar := P.wbar) hra hr hρr hμs hμ hw hwθ
        hθ.2 hc hq hQ h36' hmK hm' hBw
      linarith [hVbar, core]
    · rcases le_or_gt w P.wbar with hwb | hwb
      · have hL : HasDerivAt (fun y => P.Vbar + mK * (y - P.wbar)) mK w := by
          simpa using (((hasDerivAt_id' w).sub_const P.wbar).const_mul mK).const_add P.Vbar
        have hev : P.VI40 cK mK θK =ᶠ[𝓝[Set.Iic w] w] fun y => P.Vbar + mK * (y - P.wbar) := by
          have h1 : ∀ᶠ y in 𝓝[Set.Iic w] w, θK < y := nhdsWithin_le_nhds (Ioi_mem_nhds hwθ)
          have h2 : ∀ᶠ y in 𝓝[Set.Iic w] w, y ≤ w := self_mem_nhdsWithin
          filter_upwards [h1, h2] with y hy1 hy2
          exact hVI_mid y hy1 (hy2.trans hwb)
        have hder := hdW _ _ _ _ hL hev (hVI_mid w hwθ hwb)
        rw [hder, hVIβ, hVI_mid w hwθ hwb]
        have : 0 ≤ (P.wbar - w) * ((P.ρ - P.r - P.μ) * mK - (P.ρ - P.r)) :=
          mul_nonneg (by linarith) (by linarith)
        linarith [hVbar, this]
      · have hev : P.VI40 cK mK θK =ᶠ[𝓝[Set.Iic w] w] fun _ => P.Vbar := by
          have h1 : ∀ᶠ y in 𝓝[Set.Iic w] w, P.wbar < y := nhdsWithin_le_nhds (Ioi_mem_nhds hwb)
          filter_upwards [h1] with y hy1
          exact hVI_hi y hy1
        have hder := hdW _ _ _ _ (hasDerivAt_const w P.Vbar) hev (hVI_hi w hwb)
        rw [hder, hVIβ, hVI_hi w hwb]
        have : 0 ≤ (P.ρ - P.r) * (w - P.wbar) := mul_nonneg (by linarith) (by linarith)
        linarith [hVbar, this]
  · -- (20) for `V_∅`
    unfold Params.A0
    rcases le_or_gt w P.wbar with hwb | hwb
    · have hder : derivWithin (P.V039 cK) (Set.Iic w) w = 1 + cK * (a * w ^ (a - 1)) :=
        hdW _ _ _ _ (hVc_deriv w hw)
          (eventually_nhdsWithin_of_forall fun y hy => hV0_lo y (le_trans hy hwb))
          (hV0_lo w hwb)
      rw [hder, hV0_lo w hwb, hVc_val w hw]
      have hρa : P.ρ * a = P.r := hra.symm
      have : P.r * (P.vlow + w + cK * (w * w ^ (a - 1))) - P.ρ * w * (1 + cK * (a * w ^ (a - 1)))
          + (P.ρ - P.r) * w - P.R * P.μlow = 0 := by
        linear_combination hvlow - cK * w * w ^ (a - 1) * hρa
      linarith
    · have hev : P.V039 cK =ᶠ[𝓝[Set.Iic w] w] fun _ => P.Vbar - P.K := by
        have h1 : ∀ᶠ y in 𝓝[Set.Iic w] w, P.wbar < y := nhdsWithin_le_nhds (Ioi_mem_nhds hwb)
        filter_upwards [h1] with y hy1
        exact hV0_hi y hy1
      have hder := hdW _ _ _ _ (hasDerivAt_const w (P.Vbar - P.K)) hev (hV0_hi w hwb)
      rw [hder, hV0_hi w hwb]
      have hK2 : P.K < P.Vbar - P.vlow - P.wbar := hK.2
      have h1 : P.r * P.K < P.r * (P.Vbar - P.vlow - P.wbar) := mul_lt_mul_of_pos_left hK2 hr
      have h3 : 0 ≤ (P.ρ - P.r) * w := mul_nonneg (by linarith) (by linarith)
      have h4 : 0 < P.r * P.wbar := mul_pos hr hwpos
      nlinarith [hvlow]
  · -- (21)
    rcases le_or_gt w θK with hwθ | hwθ
    · rw [hVI_lo w hwθ, hV0_lo w (by linarith)]
      constructor
      · simp
      · simp only [sub_self]; exact hK0.le
    · rcases le_or_gt w P.wbar with hwb | hwb
      · rw [hVI_mid w hwθ hwb, hV0_lo w hwb]
        have hwpos' : 0 < w := by linarith
        have h36' : P.vlow + θK + cK * (θK * θK ^ (a - 1)) = P.Vbar + mK * (θK - P.wbar) := by
          rw [← hVc_val θK hθ.1]; exact h36
        have hcw := hVc_val w hwpos'
        have hc38 := hVc_val P.wbar hwpos
        rw [h38] at hc38
        -- lower bound: tangent at θK
        have hT1 := sc5_tangent ha0.le ha1.le hwpos' hθ.1
        rw [hpow w hwpos'] at hT1
        -- upper bound: tangent at w, then compare slopes
        have hT2 := sc5_tangent ha0.le ha1.le hwpos hwpos'
        rw [hpow P.wbar hwpos] at hT2
        have hslope : w ^ (a - 1) ≤ θK ^ (a - 1) :=
          Real.rpow_le_rpow_of_nonpos hθ.1 hwθ.le (by linarith)
        have hcT1 := mul_le_mul_of_nonneg_left hT1 hc.le
        have hcT2 := mul_le_mul_of_nonneg_left hT2 hc.le
        have hsl : cK * (a * w ^ (a - 1) * (P.wbar - w))
            ≤ cK * (a * θK ^ (a - 1) * (P.wbar - w)) := by
          apply mul_le_mul_of_nonneg_left _ hc.le
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hslope ha0.le
        have hmw1 : (mK - 1) * (w - θK) = cK * (a * θK ^ (a - 1) * (w - θK)) := by
          rw [← hmK]; ring
        have hmw2 : (mK - 1) * (P.wbar - w) = cK * (a * θK ^ (a - 1) * (P.wbar - w)) := by
          rw [← hmK]; ring
        rw [hcw]
        constructor
        · linarith [hmw1, hcT1, h36']
        · linarith [hmw2, hcT2, hsl, hc38]
      · rw [hVI_hi w hwb, hV0_hi w hwb]
        constructor
        · linarith
        · linarith
  · rw [hVI_lo 0 hθ.1.le, hVc0]
  · rw [hV0_lo 0 hwpos.le, hVc0]
