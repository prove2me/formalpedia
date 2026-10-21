-- Prove2me | solution 1 for PriceMatchNeg.Symmetric.sn_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:46:01.404923+00:00
-- url     : https://prove2.me/submissions/f4ac9715-6156-4b24-9062-b43e8037cd06

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_Model

namespace PriceMatchNeg.Symmetric

open Filter Topology





lemma nashProd_pos' {θ u v : ℝ} (hu : 0 < u) (hv : 0 < v) : 0 < nashProd θ u v := by
  unfold nashProd; positivity

lemma nashProd_zero_left' {θ v : ℝ} (hθ : 0 < θ) : nashProd θ 0 v = 0 := by
  unfold nashProd; rw [Real.zero_rpow hθ.ne']; simp

lemma nashProd_zero_right' {θ u : ℝ} (hθ : θ < 1) : nashProd θ u 0 = 0 := by
  unfold nashProd; rw [Real.zero_rpow (by linarith)]; simp

lemma log_nashProd' {θ u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.log (nashProd θ u v) = θ * Real.log u + (1 - θ) * Real.log v := by
  unfold nashProd
  rw [Real.log_mul (Real.rpow_pos_of_pos hu _).ne' (Real.rpow_pos_of_pos hv _).ne',
    Real.log_rpow hu, Real.log_rpow hv]

lemma nashProd_le_of_log' {θ u v u0 v0 : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu0 : 0 < u0)
    (hv0 : 0 < v0) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : 0 < u → 0 < v →
      θ * Real.log u + (1 - θ) * Real.log v ≤ θ * Real.log u0 + (1 - θ) * Real.log v0) :
    nashProd θ u v ≤ nashProd θ u0 v0 := by
  rcases hu.eq_or_lt with rfl | hu'
  · rw [nashProd_zero_left' hθ0]; exact (nashProd_pos' hu0 hv0).le
  rcases hv.eq_or_lt with rfl | hv'
  · rw [nashProd_zero_right' hθ1]; exact (nashProd_pos' hu0 hv0).le
  have := h hu' hv'
  rw [← log_nashProd' hu' hv', ← log_nashProd' hu0 hv0] at this
  exact (Real.log_le_log_iff (nashProd_pos' hu' hv') (nashProd_pos' hu0 hv0)).1 this

/-- Characterization of the generalized Nash bargaining solution when the buyer's payoff is a
positive multiple of the square of an affine decreasing function and the seller's gain is a concave
quadratic. -/
theorem nb_iff {θ cU y0 k g0 g1 c d : ℝ} {U V : ℝ → ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcU : 0 < cU) (hk : 0 < k) (hc : 0 < c) (hg0 : g0 ≤ 0) (hg1 : 0 ≤ g1)
    (hpk : g1 * k < 2 * c * y0)
    (hU : ∀ w, U w = cU * (y0 - k * w) ^ 2) (hV : ∀ w, V w - d = g0 + g1 * w - c * w ^ 2)
    (hex : ∃ w, 0 ≤ w ∧ 0 < y0 - k * w ∧ 0 < g0 + g1 * w - c * w ^ 2) (w : ℝ) :
    IsNashBargain θ U V d w ↔ 0 < w ∧ 0 < y0 - k * w ∧ 0 < g0 + g1 * w - c * w ^ 2 ∧
      (1 - θ) * (y0 - k * w) * (g1 - 2 * c * w) = 2 * θ * k * (g0 + g1 * w - c * w ^ 2) := by
  constructor
  · rintro ⟨⟨hw0, hUw, hVw⟩, hmax⟩
    obtain ⟨we, hwe0, hye, hGe⟩ := hex
    have hpe : 0 < nashProd θ (U we) (V we - d) :=
      nashProd_pos' (by rw [hU]; positivity) (by rw [hV]; exact hGe)
    have hmw := hmax we ⟨hwe0, by rw [hU]; positivity, by linarith [hV we]⟩
    have hGw : 0 < V w - d := by
      rcases (sub_nonneg.2 hVw).eq_or_lt with h | h
      · rw [← h, nashProd_zero_right' hθ1] at hmw; linarith
      · exact h
    have hUw' : 0 < U w := by
      rcases hUw.eq_or_lt with h | h
      · rw [← h, nashProd_zero_left' hθ0] at hmw; linarith
      · exact h
    have hy0 : y0 - k * w ≠ 0 := by intro h; rw [hU, h] at hUw'; simp at hUw'
    have hGw' := hGw
    rw [hV] at hGw'
    have hwpos : 0 < w := by
      rcases hw0.eq_or_lt with h | h
      · subst h; simp at hGw'; linarith
      · exact h
    have hy : 0 < y0 - k * w := by
      by_contra hneg
      have hlt : y0 - k * w < 0 := lt_of_le_of_ne (not_lt.1 hneg) hy0
      set w2 := (2 * y0 - k * w) / k with hw2
      have hkw2 : k * w2 = 2 * y0 - k * w := by rw [hw2]; field_simp
      have hy2 : y0 - k * w2 = -(y0 - k * w) := by linarith
      have hdiff : k ^ 2 * ((g0 + g1 * w2 - c * w2 ^ 2) - (g0 + g1 * w - c * w ^ 2)) =
          2 * (y0 - k * w) * (g1 * k - 2 * c * y0) := by
        have : k ^ 2 * ((g0 + g1 * w2 - c * w2 ^ 2) - (g0 + g1 * w - c * w ^ 2)) =
            (k * w2 - k * w) * (g1 * k - c * (k * w2 + k * w)) := by ring
        rw [this, hkw2]; ring
      have hpos : 0 < 2 * (y0 - k * w) * (g1 * k - 2 * c * y0) := by nlinarith
      have hG2 : (g0 + g1 * w - c * w ^ 2) < g0 + g1 * w2 - c * w2 ^ 2 := by
        rw [← hdiff] at hpos
        have := (mul_pos_iff_of_pos_left (by positivity : (0:ℝ) < k ^ 2)).1 hpos
        linarith
      have hw2nn : 0 ≤ w2 := by
        by_contra h2
        push Not at h2
        nlinarith
      have hU2 : U w2 = U w := by rw [hU, hU, hy2]; ring
      have hm2 := hmax w2 ⟨hw2nn, by rw [hU]; positivity, by linarith [hV w2]⟩
      rw [hU2, hV, hV] at hm2
      have : nashProd θ (U w) (g0 + g1 * w - c * w ^ 2) <
          nashProd θ (U w) (g0 + g1 * w2 - c * w2 ^ 2) := by
        unfold nashProd
        apply mul_lt_mul_of_pos_left _ (Real.rpow_pos_of_pos hUw' _)
        exact Real.rpow_lt_rpow hGw'.le hG2 (by linarith)
      linarith
    refine ⟨hwpos, hy, hGw', ?_⟩
    -- first-order condition
    set f : ℝ → ℝ := fun z =>
      θ * Real.log (cU * (y0 - k * z) ^ 2) + (1 - θ) * Real.log (g0 + g1 * z - c * z ^ 2) with hf
    have hloc : IsLocalMax f w := by
      have e1 : ∀ᶠ z in 𝓝 w, 0 < z := lt_mem_nhds hwpos
      have e2 : ∀ᶠ z in 𝓝 w, 0 < y0 - k * z :=
        ContinuousAt.eventually_lt (f := fun _ => (0:ℝ)) (g := fun z => y0 - k * z)
          (by fun_prop) (by fun_prop) hy
      have e3 : ∀ᶠ z in 𝓝 w, 0 < g0 + g1 * z - c * z ^ 2 :=
        ContinuousAt.eventually_lt (f := fun _ => (0:ℝ)) (g := fun z => g0 + g1 * z - c * z ^ 2)
          (by fun_prop) (by fun_prop) hGw'
      filter_upwards [e1, e2, e3] with z hz1 hz2 hz3
      have hm := hmax z ⟨hz1.le, by rw [hU]; positivity, by linarith [hV z]⟩
      rw [hU, hU, hV, hV] at hm
      have hm' := Real.log_le_log (nashProd_pos' (by positivity) hz3) hm
      rw [log_nashProd' (by positivity) hz3, log_nashProd' (by positivity) hGw'] at hm'
      exact hm'
    have hd1 : HasDerivAt (fun z => cU * (y0 - k * z) ^ 2) (cU * (2 * (y0 - k * w) * (-k))) w := by
      have h0 : HasDerivAt (fun z => y0 - k * z) (-k) w := by
        simpa using ((hasDerivAt_id w).const_mul k).const_sub y0
      have := (h0.pow 2).const_mul cU
      exact this.congr_deriv (by norm_num)
    have hd2 : HasDerivAt (fun z => g0 + g1 * z - c * z ^ 2) (g1 - 2 * c * w) w := by
      have := ((hasDerivAt_const w g0).add ((hasDerivAt_id' w).const_mul g1)).sub
        ((hasDerivAt_pow 2 w).const_mul c)
      exact this.congr_deriv (by norm_num; ring)
    have hcy : cU * (y0 - k * w) ^ 2 ≠ 0 := by positivity
    have hdf : HasDerivAt f (θ * (cU * (2 * (y0 - k * w) * (-k)) / (cU * (y0 - k * w) ^ 2)) +
        (1 - θ) * ((g1 - 2 * c * w) / (g0 + g1 * w - c * w ^ 2))) w :=
      ((hd1.log hcy).const_mul θ).add ((hd2.log hGw'.ne').const_mul (1 - θ))
    have h0 := hloc.hasDerivAt_eq_zero hdf
    have hyne : y0 - k * w ≠ 0 := hy.ne'
    have hGne : g0 + g1 * w - c * w ^ 2 ≠ 0 := hGw'.ne'
    generalize hYY : y0 - k * w = Y at h0 hyne hy
    generalize hGG : g0 + g1 * w - c * w ^ 2 = GG at h0 hGne hGw'
    have hcU' : cU ≠ 0 := hcU.ne'
    field_simp at h0
    have hP : g1 - 2 * c * w = g1 - 2 * c * w := rfl
    linear_combination h0
  · rintro ⟨hw, hy, hG, hfoc⟩
    refine ⟨⟨hw.le, by rw [hU]; positivity, by linarith [hV w]⟩, ?_⟩
    rintro w' ⟨hw', hU', hV'⟩
    have hG' : 0 ≤ V w' - d := by linarith
    have hUw : 0 < U w := by rw [hU]; positivity
    have hGw : 0 < V w - d := by rw [hV]; exact hG
    apply nashProd_le_of_log' hθ0 hθ1 hUw hGw hU' hG'
    intro hu hv
    set y := y0 - k * w with hydef
    set G := g0 + g1 * w - c * w ^ 2 with hGdef
    set y' := y0 - k * w' with hy'def
    have hy'ne : y' ≠ 0 := by intro h0; rw [hU, ← hy'def, h0] at hu; simp at hu
    have hlogU : Real.log (U w') - Real.log (U w) ≤ 2 * (|y'| / y - 1) := by
      rw [← Real.log_div hu.ne' hUw.ne', hU, hU]
      have : cU * y' ^ 2 / (cU * y ^ 2) = (|y'| / y) ^ 2 := by
        rw [div_pow, sq_abs]; field_simp
      rw [this, Real.log_pow]
      have hpos : 0 < |y'| / y := div_pos (abs_pos.2 hy'ne) hy
      have := Real.log_le_sub_one_of_pos hpos
      push_cast; linarith
    have hlogG : Real.log (V w' - d) - Real.log (V w - d) ≤ (V w' - d) / G - 1 := by
      rw [← Real.log_div hv.ne' hGw.ne', hV w]
      exact Real.log_le_sub_one_of_pos (div_pos hv hG)
    have key : 2 * θ * (|y'| - y) * G + (1 - θ) * ((V w' - d) - G) * y ≤ 0 := by
      rw [hV w']
      have e : 2 * θ * (y' - y) * G + (1 - θ) * ((g0 + g1 * w' - c * w' ^ 2) - G) * y =
          -((1 - θ) * c * y * (w' - w) ^ 2) := by
        rw [hy'def, hydef, hGdef]; linear_combination (w' - w) * hfoc
      have hθ' : 0 ≤ 1 - θ := by linarith
      rcases le_or_gt 0 y' with hy'0 | hy'0
      · rw [abs_of_nonneg hy'0]
        rw [e]
        have : 0 ≤ (1 - θ) * c * y * (w' - w) ^ 2 := by positivity
        linarith
      · rw [abs_of_neg hy'0]
        -- k * expr = (1-θ) y (-c k u^2 - 2 y' P)
        set P := g1 - 2 * c * w with hP
        set u := w' - w with hu'
        have hfoc' : (1 - θ) * y * P = 2 * θ * k * G := hfoc
        have hexpr : k * (2 * θ * (-y' - y) * G + (1 - θ) * ((g0 + g1 * w' - c * w' ^ 2) - G) * y)
            = (1 - θ) * y * (-(c * k * u ^ 2) - 2 * y' * P) := by
          have : 2 * θ * (-y' - y) * G + (1 - θ) * ((g0 + g1 * w' - c * w' ^ 2) - G) * y
              = -((1 - θ) * c * y * (w' - w) ^ 2) - 4 * θ * y' * G := by linear_combination e
          rw [this]; linear_combination (2 * y') * hfoc'
        have hin : 0 ≤ c * k * u ^ 2 + 2 * y' * P := by
          rcases le_or_gt P 0 with hP0 | hP0
          · nlinarith [mul_nonneg (mul_nonneg hc.le hk.le) (sq_nonneg u),
              mul_nonneg (neg_nonneg.2 hy'0.le) (neg_nonneg.2 hP0)]
          · -- y' = y - k u, kP < 2 c y
            have hyu : y' = y - k * u := by rw [hy'def, hydef, hu']; ring
            have hkP : k * P < 2 * c * y := by
              have e1 : k * P = g1 * k - 2 * c * k * w := by rw [hP]; ring
              have e2 : 2 * c * y = 2 * c * y0 - 2 * c * k * w := by rw [hydef]; ring
              linarith
            have h2 : 0 ≤ c * k * (c * k * u ^ 2 + 2 * y' * P) := by
              have : c * k * (c * k * u ^ 2 + 2 * y' * P) =
                  (c * k * u - k * P) ^ 2 + k * P * (2 * c * y - k * P) := by
                rw [hyu]; ring
              rw [this]
              have : 0 ≤ k * P * (2 * c * y - k * P) := by
                apply mul_nonneg (by positivity); linarith
              positivity
            exact (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < c * k)).1 h2
        have : k * (2 * θ * (-y' - y) * G + (1 - θ) * ((g0 + g1 * w' - c * w' ^ 2) - G) * y) ≤ 0 := by
          rw [hexpr]
          have h1y : 0 ≤ (1 - θ) * y := by positivity
          have := mul_nonneg h1y hin
          have e3 : (1 - θ) * y * (-(c * k * u ^ 2) - 2 * y' * P) =
              -((1 - θ) * y * (c * k * u ^ 2 + 2 * y' * P)) := by ring
          linarith
        by_contra hX
        push Not at hX
        have := mul_pos hk hX
        linarith
    have hcomb : θ * (2 * (|y'| / y - 1)) + (1 - θ) * ((V w' - d) / G - 1) ≤ 0 := by
      have : θ * (2 * (|y'| / y - 1)) + (1 - θ) * ((V w' - d) / G - 1) =
          (2 * θ * (|y'| - y) * G + (1 - θ) * ((V w' - d) - G) * y) / (y * G) := by
        field_simp
      rw [this]; exact div_nonpos_of_nonpos_of_nonneg key (by positivity)
    have hθ' : 0 ≤ 1 - θ := by linarith
    have i1 := mul_le_mul_of_nonneg_left hlogU hθ0.le
    have i2 := mul_le_mul_of_nonneg_left hlogG hθ'
    linarith






section Base
variable (P : Params)

lemma xHat_eq (wi wj : ℝ) : xHat P wi wj =
    ((2 - P.γ - P.γ ^ 2) * P.a - (2 - P.γ ^ 2) * wi + P.γ * wj) / ((1 - P.γ ^ 2) * (4 - P.γ ^ 2)) :=
  rfl

lemma std_facts (hS : P.Standing) :
    0 < 1 - P.γ ^ 2 ∧ 0 < 4 - P.γ ^ 2 ∧ 0 < 2 - P.γ ^ 2 ∧ 0 < 2 - P.γ - P.γ ^ 2 ∧
      0 < (1 + P.γ) * (2 - P.γ) := by
  obtain ⟨ha, hg0, hg1⟩ := hS
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

lemma demand_pHat (hS : P.Standing) (wi wj : ℝ) :
    demand P (pHat P wi wj) (pHat P wj wi) = xHat P wi wj := by
  obtain ⟨h1, h2, -, -, -⟩ := std_facts P hS
  unfold demand pHat xHat
  field_simp
  ring

lemma piB_eq (hS : P.Standing) (wi wj : ℝ) :
    piB P wi wj = (1 - P.γ ^ 2) * xHat P wi wj ^ 2 := by
  obtain ⟨h1, h2, -, -, -⟩ := std_facts P hS
  unfold piB retailProfit
  rw [demand_pHat P hS]
  unfold pHat xHat
  field_simp
  ring

lemma piS_eq (hS : P.Standing) (wi wj : ℝ) :
    piS P wi wj = wi * xHat P wi wj + wj * xHat P wj wi := by
  unfold piS
  rw [demand_pHat P hS, demand_pHat P hS]

lemma piMs_eq (w : ℝ) : piMs P w = w * (P.a - w) / 2 := by
  unfold piMs pMono; ring

lemma piMb_eq (w : ℝ) : piMb P w = (P.a - w) ^ 2 / 4 := by
  unfold piMb monoProfit pMono; ring

lemma piS_diag (hS : P.Standing) (w : ℝ) :
    piS P w w = 2 * w * (P.a - w) / ((1 + P.γ) * (2 - P.γ)) := by
  obtain ⟨h1, h2, -, -, h5⟩ := std_facts P hS
  have h1' : (1 - P.γ) ≠ 0 := by have := hS.2.2; intro h; linarith
  have h2' : (2 + P.γ) ≠ 0 := by have := hS.2.1; intro h; linarith
  have h3' : (1 + P.γ) ≠ 0 := by have := hS.2.1; intro h; linarith
  have h4' : (2 - P.γ) ≠ 0 := by have := hS.2.2; intro h; linarith
  rw [piS_eq P hS, xHat_eq]
  have e1 : (1 - P.γ ^ 2) * (4 - P.γ ^ 2) = (1 - P.γ) * (1 + P.γ) * (2 - P.γ) * (2 + P.γ) := by ring
  rw [e1]
  field_simp
  ring

lemma piB_diag (hS : P.Standing) (w : ℝ) :
    piB P w w = (1 - P.γ) * (P.a - w) ^ 2 / ((1 + P.γ) * (2 - P.γ) ^ 2) := by
  have h1' : (1 - P.γ) ≠ 0 := by have := hS.2.2; intro h; linarith
  have h2' : (2 + P.γ) ≠ 0 := by have := hS.2.1; intro h; linarith
  have h3' : (1 + P.γ) ≠ 0 := by have := hS.2.1; intro h; linarith
  have h4' : (2 - P.γ) ≠ 0 := by have := hS.2.2; intro h; linarith
  rw [piB_eq P hS, xHat_eq]
  have e1 : (1 - P.γ ^ 2) * (4 - P.γ ^ 2) = (1 - P.γ) * (1 + P.γ) * (2 - P.γ) * (2 + P.γ) := by ring
  rw [e1]
  field_simp
  ring

end Base






/-- `D² ×` (first-order condition) of the SN bargain over `w` given the rival price `t`. -/
noncomputable def snFoc (a γ θ w t : ℝ) : ℝ :=
  -a^2*γ^4*θ + a^2*γ^4 - 2*a^2*γ^3*θ + 2*a^2*γ^3 + 3*a^2*γ^2*θ - 3*a^2*γ^2 + 4*a^2*γ*θ -
  4*a^2*γ - 4*a^2*θ + 4*a^2 - a*γ^6*t*θ + 5*a*γ^4*t*θ + a*γ^4*θ*w - 3*a*γ^4*w + a*γ^3*t*θ -
  3*a*γ^3*t + a*γ^3*θ*w - 3*a*γ^3*w - 3*a*γ^2*t*θ - 3*a*γ^2*t - 4*a*γ^2*θ*w + 12*a*γ^2*w -
  2*a*γ*t*θ + 6*a*γ*t - 2*a*γ*θ*w + 6*a*γ*w + 4*a*θ*w - 12*a*w + γ^6*t^2*θ - 5*γ^4*t^2*θ +
  2*γ^4*w^2 + 4*γ^3*t*w + 4*γ^2*t^2*θ + 2*γ^2*t^2 - 8*γ^2*w^2 - 8*γ*t*w + 8*w^2

lemma sn_bargain_iff (a γ : ℝ) (hS : Params.Standing ⟨a, γ⟩) (θ : ℝ) (hθ : ValidPower θ)
    (t : ℝ) (ht0 : 0 ≤ t) (hta : t ≤ a) (w : ℝ) :
    IsNashBargain θ (fun w => piB ⟨a, γ⟩ w t) (fun w => piS ⟨a, γ⟩ w t) (piMs ⟨a, γ⟩ t) w ↔
      0 < w ∧ 0 < (2 - γ - γ ^ 2) * a + γ * t - (2 - γ ^ 2) * w ∧
        0 < (2 - γ - γ ^ 2) * a + 2 * γ * t - 2 * (2 - γ ^ 2) * w ∧ snFoc a γ θ w t = 0 := by
  obtain ⟨h1, h2, h3, hK, hs⟩ := std_facts ⟨a, γ⟩ hS
  obtain ⟨ha, hγ0, hγ1⟩ := hS
  obtain ⟨hθ0, hθ1⟩ := hθ
  dsimp only at h1 h2 h3 hK hs ha hγ0 hγ1
  set D := (1 - γ ^ 2) * (4 - γ ^ 2) with hD
  set K := 2 - γ - γ ^ 2 with hKd
  set m := 2 - γ ^ 2 with hm
  have hD0 : 0 < D := mul_pos h1 h2
  have hS' : Params.Standing ⟨a, γ⟩ := ⟨ha, hγ0, hγ1⟩
  have hg0 : t * (K * a - m * t) / D - t * (a - t) / 2 ≤ 0 := by
    have e : t * (K * a - m * t) / D - t * (a - t) / 2 =
        -(t * (a * γ * (1 - γ) ^ 2 * (2 + γ) + t * γ ^ 2 * (3 - γ ^ 2))) / (2 * D) := by
      rw [hD, hKd, hm]; field_simp; ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have : 0 ≤ 3 - γ ^ 2 := by nlinarith
    have : 0 ≤ 2 + γ := by linarith
    have : 0 ≤ t * (a * γ * (1 - γ) ^ 2 * (2 + γ) + t * γ ^ 2 * (3 - γ ^ 2)) := by positivity
    linarith
  have hpk : (K * a + 2 * γ * t) / D * (m / D) < 2 * (m / D) * ((K * a + γ * t) / D) := by
    have e : 2 * (m / D) * ((K * a + γ * t) / D) - (K * a + 2 * γ * t) / D * (m / D) =
        m * K * a / D ^ 2 := by field_simp; ring
    have : 0 < m * K * a / D ^ 2 := by positivity
    linarith
  have hex : ∃ v, 0 ≤ v ∧ 0 < (K * a + γ * t) / D - m / D * v ∧
      0 < t * (K * a - m * t) / D - t * (a - t) / 2 + (K * a + 2 * γ * t) / D * v -
        m / D * v ^ 2 := by
    refine ⟨(K * a + 2 * γ * t) / (2 * m), by positivity, ?_, ?_⟩
    · have e : (K * a + γ * t) / D - m / D * ((K * a + 2 * γ * t) / (2 * m)) = K * a / (2 * D) := by
        field_simp; ring
      rw [e]; positivity
    · have e : t * (K * a - m * t) / D - t * (a - t) / 2 + (K * a + 2 * γ * t) / D *
          ((K * a + 2 * γ * t) / (2 * m)) - m / D * ((K * a + 2 * γ * t) / (2 * m)) ^ 2 =
          (a ^ 2 * K + 2 * γ ^ 2 * ((1 + γ) * (2 - γ)) * (t * (a - t))) / (4 * m * ((1 + γ) * (2 - γ))) := by
        rw [hD, hKd, hm]
        have : (1 + γ) ≠ 0 := by intro h; linarith
        have : (2 - γ) ≠ 0 := by intro h; linarith
        have : (1 - γ) ≠ 0 := by intro h; linarith
        have : (2 + γ) ≠ 0 := by intro h; linarith
        have : (2 - γ ^ 2) ≠ 0 := by intro h; nlinarith
        have e1 : (1 - γ ^ 2) * (4 - γ ^ 2) = (1 - γ) * (1 + γ) * (2 - γ) * (2 + γ) := by ring
        rw [e1]
        field_simp
        ring
      rw [e]
      have : 0 ≤ t * (a - t) := mul_nonneg ht0 (by linarith)
      positivity
  rw [nb_iff (cU := 1 - γ ^ 2) (y0 := (K * a + γ * t) / D) (k := m / D)
    (g0 := t * (K * a - m * t) / D - t * (a - t) / 2) (g1 := (K * a + 2 * γ * t) / D) (c := m / D)
    hθ0 hθ1 h1 (by positivity) (by positivity) hg0 (by positivity) hpk
    (fun v => by
      rw [piB_eq ⟨a, γ⟩ hS', xHat_eq]
      try dsimp only
      rw [hD, hKd, hm]; ring)
    (fun v => by
      rw [piS_eq ⟨a, γ⟩ hS', xHat_eq, xHat_eq, piMs_eq]
      try dsimp only
      rw [hD, hKd, hm]; ring) hex w]
  -- translate the conditions
  have ey : (K * a + γ * t) / D - m / D * w = (K * a + γ * t - m * w) / D := by ring
  have eP : (K * a + 2 * γ * t) / D - 2 * (m / D) * w = (K * a + 2 * γ * t - 2 * m * w) / D := by
    ring
  have eF : D ^ 2 * ((1 - θ) * ((K * a + γ * t) / D - m / D * w) *
      ((K * a + 2 * γ * t) / D - 2 * (m / D) * w) - 2 * θ * (m / D) *
      (t * (K * a - m * t) / D - t * (a - t) / 2 + (K * a + 2 * γ * t) / D * w - m / D * w ^ 2)) =
      snFoc a γ θ w t := by
    rw [snFoc, hD, hKd, hm]; field_simp; ring
  constructor
  · rintro ⟨hw, hy, hG, hfoc⟩
    have hy' : 0 < K * a + γ * t - m * w := by
      rw [ey] at hy; exact (div_pos_iff_of_pos_right hD0).1 hy
    have hfoc' := hfoc
    rw [← sub_eq_zero] at hfoc'
    have hF0 : snFoc a γ θ w t = 0 := by
      rw [← eF]
      have : (1 - θ) * ((K * a + γ * t) / D - m / D * w) * ((K * a + 2 * γ * t) / D - 2 * (m / D) * w)
          - 2 * θ * (m / D) * (t * (K * a - m * t) / D - t * (a - t) / 2 +
            (K * a + 2 * γ * t) / D * w - m / D * w ^ 2) = 0 := by
        rw [← hfoc']
      rw [this, mul_zero]
    refine ⟨hw, hy', ?_, hF0⟩
    have hpos : 0 < (1 - θ) * ((K * a + γ * t) / D - m / D * w) *
        ((K * a + 2 * γ * t) / D - 2 * (m / D) * w) := by
      rw [hfoc]
      have : 0 < 2 * θ * (m / D) := by positivity
      positivity
    have h1y : 0 < (1 - θ) * ((K * a + γ * t) / D - m / D * w) :=
      mul_pos (by linarith) hy
    have hP := pos_of_mul_pos_right hpos h1y.le
    rw [eP] at hP
    exact (div_pos_iff_of_pos_right hD0).1 hP
  · rintro ⟨hw, hy, hP, hF0⟩
    have hy' : 0 < (K * a + γ * t) / D - m / D * w := by rw [ey]; positivity
    have hP' : 0 < (K * a + 2 * γ * t) / D - 2 * (m / D) * w := by rw [eP]; positivity
    have hfoc : (1 - θ) * ((K * a + γ * t) / D - m / D * w) *
        ((K * a + 2 * γ * t) / D - 2 * (m / D) * w) = 2 * θ * (m / D) *
        (t * (K * a - m * t) / D - t * (a - t) / 2 + (K * a + 2 * γ * t) / D * w - m / D * w ^ 2) := by
      rw [← eF] at hF0
      have := (mul_eq_zero.1 hF0).resolve_left (by positivity)
      linarith
    refine ⟨hw, hy', ?_, hfoc⟩
    have hpos : 0 < (1 - θ) * ((K * a + γ * t) / D - m / D * w) *
        ((K * a + 2 * γ * t) / D - 2 * (m / D) * w) :=
      mul_pos (mul_pos (by linarith) hy') hP'
    rw [hfoc] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)

theorem sn_equilibrium' (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : ValidPower θ) :
    ∀ w1 w2, IsSNEq P θ θ w1 w2 ↔ w1 = wSN P θ ∧ w2 = wSN P θ := by
  rcases P with ⟨a, γ⟩
  intro w1 w2
  obtain ⟨h1, h2, h3, hK0, hs0⟩ := std_facts ⟨a, γ⟩ hS
  have hS' := hS
  obtain ⟨ha, hγ0, hγ1⟩ := hS'
  have hθ' := hθ
  obtain ⟨hθ0, hθ1⟩ := hθ'
  dsimp only at ha hγ0 hγ1 h1 h2 h3 hK0 hs0
  have hE0 : 0 < 2 * (2 - γ - γ ^ 2) + γ ^ 2 * ((1 + γ) * (2 - γ)) * θ := by
    have : 0 ≤ γ ^ 2 * ((1 + γ) * (2 - γ)) * θ := by positivity
    linarith
  have hwSN : wSN ⟨a, γ⟩ θ =
      (1 - θ) * (2 - γ - γ ^ 2) * a / (2 * (2 - γ - γ ^ 2) + γ ^ 2 * ((1 + γ) * (2 - γ)) * θ) := by
    rw [wSN]; dsimp only; ring
  set K := 2 - γ - γ ^ 2 with hK
  set E := 2 * K + γ ^ 2 * ((1 + γ) * (2 - γ)) * θ with hE
  have hdiag : ∀ w, snFoc a γ θ w w = (w - a) * (γ - 1) * (γ + 2) * ((1 - θ) * K * a - E * w) := by
    intro w; rw [snFoc, hE, hK]; ring
  have hwpos : 0 < (1 - θ) * K * a / E := by
    have : 0 < 1 - θ := by linarith
    positivity
  have hwhalf : (1 - θ) * K * a / E < a / 2 := by
    rw [div_lt_div_iff₀ hE0 (by norm_num)]
    have : 0 < θ * K * a := by positivity
    have : 0 ≤ γ ^ 2 * ((1 + γ) * (2 - γ)) * θ * a := by positivity
    rw [hE]; nlinarith
  unfold IsSNEq
  constructor
  · rintro ⟨⟨h10, h1a⟩, ⟨h20, h2a⟩, hb1, hb2⟩
    rw [sn_bargain_iff a γ hS θ hθ w2 h20 h2a] at hb1
    rw [sn_bargain_iff a γ hS θ hθ w1 h10 h1a] at hb2
    obtain ⟨-, -, hP1, hF1⟩ := hb1
    obtain ⟨-, -, hP2, hF2⟩ := hb2
    have hsum : w1 + w2 < a := by
      have : K * (w1 + w2) < K * a := by rw [hK]; linarith
      exact lt_of_mul_lt_mul_left this hK0.le
    have hasym : snFoc a γ θ w1 w2 - snFoc a γ θ w2 w1 = (1 - γ ^ 2) * (4 - γ ^ 2) * (w2 - w1) *
        (3 * a - a * θ * (1 + γ ^ 2) - (2 - γ ^ 2 * θ) * (w1 + w2)) := by
      rw [snFoc, snFoc]; ring
    have hM : 0 < 3 * a - a * θ * (1 + γ ^ 2) - (2 - γ ^ 2 * θ) * (w1 + w2) := by
      have hg2 : 0 < 2 - γ ^ 2 * θ := by nlinarith
      have := mul_lt_mul_of_pos_left hsum hg2
      have : 0 < a * (1 - θ) := mul_pos ha (by linarith)
      nlinarith
    rw [hF1, hF2, sub_zero] at hasym
    have h12 : w2 - w1 = 0 := by
      rcases mul_eq_zero.1 hasym.symm with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' (mul_pos h1 h2).ne'
        · exact h'
      · exact absurd h hM.ne'
    have hw12 : w2 = w1 := by linarith
    subst hw12
    have hd := hdiag w2
    rw [hF1] at hd
    have hw2a : w2 - a ≠ 0 := by intro h; linarith
    have hL : (1 - θ) * K * a - E * w2 = 0 := by
      rcases mul_eq_zero.1 hd.symm with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · rcases mul_eq_zero.1 h' with h'' | h''
          · exact absurd h'' hw2a
          · exact absurd h'' (by intro h; linarith)
        · exact absurd h' (by intro h; linarith)
      · exact h
    have : w2 = (1 - θ) * K * a / E := by
      field_simp; linarith
    rw [hwSN]; exact ⟨this, this⟩
  · rintro ⟨rfl, rfl⟩
    rw [hwSN]
    have hmem0 : 0 ≤ (1 - θ) * K * a / E := hwpos.le
    have hmema : (1 - θ) * K * a / E ≤ a := by linarith
    have hb : IsNashBargain θ (fun w => piB ⟨a, γ⟩ w ((1 - θ) * K * a / E))
        (fun w => piS ⟨a, γ⟩ w ((1 - θ) * K * a / E)) (piMs ⟨a, γ⟩ ((1 - θ) * K * a / E))
        ((1 - θ) * K * a / E) := by
      rw [sn_bargain_iff a γ hS θ hθ _ hmem0 hmema]
      refine ⟨hwpos, ?_, ?_, ?_⟩
      · have e : (2 - γ - γ ^ 2) * a + γ * ((1 - θ) * K * a / E) - (2 - γ ^ 2) * ((1 - θ) * K * a / E)
            = K * (a - (1 - θ) * K * a / E) := by rw [hK]; ring
        rw [e]; exact mul_pos hK0 (by linarith)
      · have e : (2 - γ - γ ^ 2) * a + 2 * γ * ((1 - θ) * K * a / E) -
            2 * (2 - γ ^ 2) * ((1 - θ) * K * a / E) = K * (a - 2 * ((1 - θ) * K * a / E)) := by
          rw [hK]; ring
        rw [e]; exact mul_pos hK0 (by linarith)
      · rw [hdiag]
        have : (1 - θ) * K * a - E * ((1 - θ) * K * a / E) = 0 := by field_simp; ring
        rw [this, mul_zero]
    exact ⟨⟨hmem0, hmema⟩, ⟨hmem0, hmema⟩, hb, hb⟩



end PriceMatchNeg.Symmetric

open PriceMatchNeg.Symmetric

theorem solution (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : ValidPower θ) :
    ∀ w1 w2, IsSNEq P θ θ w1 w2 ↔ w1 = wSN P θ ∧ w2 = wSN P θ := sn_equilibrium' P hS θ hθ
