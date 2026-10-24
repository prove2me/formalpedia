-- Prove2me | solution 1 for QualityEncroach.Uniform.proposition_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T15:45:24.05095+00:00
-- url     : https://prove2.me/submissions/c61122be-a4b6-4c06-b22b-2e96027c1cec

import Mathlib
import Definitions.Def_QualityEncroach_Uniform_Game

set_option autoImplicit false

namespace QE38

open QualityEncroach.Uniform

/-! ## Pure algebra -/

lemma quad_max (α β q T : ℝ) (hβ : 0 < β) (hq : 0 ≤ q) (hqT : q < T)
    (h : ∀ x, 0 ≤ x → x < T → α*x - β*x^2 ≤ α*q - β*q^2) :
    α - 2*β*q ≤ 0 ∧ (0 < q → α - 2*β*q = 0) := by
  have hA : α - 2*β*q ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨t, ht⟩ : ∃ t, t = min ((α - 2*β*q)/(2*β)) ((T-q)/2) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact lt_min (div_pos hpos (by linarith)) (by linarith)
    have ht1 : t ≤ (α - 2*β*q)/(2*β) := by rw [ht]; exact min_le_left _ _
    have ht2 : t ≤ (T-q)/2 := by rw [ht]; exact min_le_right _ _
    have ht1' : 2*β*t ≤ α - 2*β*q := by
      have := (le_div_iff₀ (by linarith : (0:ℝ) < 2*β)).1 ht1; linarith
    have := h (q+t) (by linarith) (by linarith)
    nlinarith [mul_pos ht0 hpos, mul_nonneg ht0.le (sub_nonneg.2 ht1')]
  refine ⟨hA, fun hq0 => ?_⟩
  by_contra hne
  have hneg : α - 2*β*q < 0 := lt_of_le_of_ne hA hne
  obtain ⟨t, ht⟩ : ∃ t, t = min q (-(α - 2*β*q)/(2*β)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact lt_min hq0 (div_pos (by linarith) (by linarith))
  have ht1 : t ≤ q := by rw [ht]; exact min_le_left _ _
  have ht2 : t ≤ -(α - 2*β*q)/(2*β) := by rw [ht]; exact min_le_right _ _
  have ht2' : 2*β*t ≤ -(α - 2*β*q) := by
    have := (le_div_iff₀ (by linarith : (0:ℝ) < 2*β)).1 ht2; linarith
  have := h (q-t) (by linarith) (by linarith)
  nlinarith [mul_pos ht0 (neg_pos.2 hneg), mul_nonneg ht0.le (sub_nonneg.2 ht2')]

-- bad critical points with v ≤ 6/25 are beaten by the encroach deviation at u = 1/3
lemma core_bad1 (d v : ℝ) (hv : 0 < v) (hd : 0 ≤ d)
    (hfoc : 9*v^4 - 12*v^3 + (3+6*d)*v^2 - 7*d^2 = 0)
    (hreg : 5*d < 3*v*(1-v)) (hbad : v ≤ 24*d^2) (hle : v ≤ 6/25)
    (h13 : 1/27 - d/3 + 7*d^2/4 ≤ (1/2 - v)*(v - v^2 - d)) : False := by
  nlinarith [sq_nonneg (v - 1/5), sq_nonneg (d - 1/11), mul_pos hv hv, sq_nonneg (v - 6*d/5 + 1/10),
    mul_nonneg hd hv.le, mul_nonneg (sub_nonneg.2 hle) hv.le, mul_nonneg (sub_nonneg.2 hle) hd]

-- critical points with v ≥ 13/50 are never bad
lemma vhiA (d v : ℝ) (hv : 13/50 ≤ v) (hd : 0 ≤ d)
    (hfoc : 9*v^4 - 12*v^3 + (3+6*d)*v^2 - 7*d^2 = 0)
    (hreg : 5*d < 3*v*(1-v)) (hbad : v ≤ 24*d^2) : False := by
  nlinarith [mul_nonneg (sub_nonneg.2 hbad) hd, mul_nonneg (sub_nonneg.2 hbad) (sub_nonneg.2 hv),
    mul_nonneg (sub_nonneg.2 hv) hd, sq_nonneg (d - 1/10), sq_nonneg (v - 3/10), mul_nonneg hd hd]

-- bad critical points with 6/25 ≤ v < 13/50 are beaten by the deterrence deviation at u = 21/100
lemma core_bad2 (d v : ℝ) (hv : 0 < v) (hd : 0 ≤ d)
    (hfoc : 9*v^4 - 12*v^3 + (3+6*d)*v^2 - 7*d^2 = 0)
    (hreg : 5*d < 3*v*(1-v)) (hbad : v ≤ 24*d^2) (hge : 6/25 ≤ v) (hv1 : v ≤ 13/50)
    (hz : ((21/100)^2/2 - (21/100)/2 + 3*d/2) * (1 - 100*d/21 - 21/100) ≤ (1/2 - v)*(v - v^2 - d)) :
    False := by
  have hd1 : 1/10 ≤ d := by nlinarith
  have hd2 : d ≤ 21/200 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hge) (sub_nonneg.2 hv1), mul_nonneg (sub_nonneg.2 hd1) (sub_nonneg.2 hd2),
    mul_nonneg (sub_nonneg.2 hge) (sub_nonneg.2 hd2), mul_nonneg (sub_nonneg.2 hd1) (sub_nonneg.2 hv1),
    mul_nonneg (sub_nonneg.2 hge) (sub_nonneg.2 hd1), mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hd2)]

lemma final_alg (d v m : ℝ) (hv : 0 < v) (hd : 0 ≤ d) (hreg : 5*d < 3*v - 3*v^2)
    (hfoc : 9*v^4 - 12*v^3 + (3+6*d)*v^2 - 7*d^2 = 0)
    (hm : 12*v*m = 3*v^4 - 6*v^3 + (3+6*d)*v^2 - 6*d*v + 7*d^2)
    (h13 : 15*d < 2 → 1/27 - d/3 + 7*d^2/4 ≤ m)
    (hz21 : (21/100)*(1 - 3*(1 - d/(21/100) - 21/100)/2 - 21/100)*(1 - d/(21/100) - 21/100) ≤ m)
    (hz3 : (1/3)*(1 - 3*(1 - d/(1/3) - 1/3)/2 - 1/3)*(1 - d/(1/3) - 1/3) ≤ m) :
    1 < 54*m ∧ 24*d^2 < v := by
  have hm0 : 12*v*(m - (1/2 - v)*(v - v^2 - d)) = 0 := by linear_combination hm - hfoc
  have hmP : m = (1/2 - v)*(v - v^2 - d) := by
    rcases mul_eq_zero.1 hm0 with h | h
    · nlinarith
    · linarith
  have hreg' : 5*d < 3*v*(1-v) := by nlinarith
  have hd3 : d < 3/20 := by nlinarith [sq_nonneg (v - 1/2)]
  refine ⟨?_, ?_⟩
  · by_cases h15 : 15*d < 2
    · have := h13 h15
      nlinarith [sq_nonneg (d - 2/21)]
    · push Not at h15
      have e : (1/3)*(1 - 3*(1 - d/(1/3) - 1/3)/2 - 1/3)*(1 - d/(1/3) - 1/3)
          = (3*d/2 - 1/9)*(2/3 - 3*d) := by ring
      rw [e] at hz3
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2/15) (by linarith : (0:ℝ) ≤ 3/20 - d)]
  · by_contra hbad
    push Not at hbad
    rcases le_or_gt v (6/25) with hle | hgt
    · have h15 : 15*d < 2 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 6/25 - v) (by linarith : (0:ℝ) ≤ 19/25 - v)]
      have := h13 h15
      rw [hmP] at this
      exact core_bad1 d v hv hd hfoc hreg' hbad hle this
    · have hv1 : v ≤ 13/50 := by
        by_contra hh
        push Not at hh
        exact vhiA d v hh.le hd hfoc hreg' hbad
      have e : (21/100)*(1 - 3*(1 - d/(21/100) - 21/100)/2 - 21/100)*(1 - d/(21/100) - 21/100)
          = ((21/100)^2/2 - (21/100)/2 + 3*d/2) * (1 - 100*d/21 - 21/100) := by ring
      rw [e, hmP] at hz21
      exact core_bad2 d v hv hd hfoc hreg' hbad hgt.le hv1 hz21

/-! ## The game -/

def NN (k c x : ℝ) : ℝ := 3*k^2*x^4 - 6*k*x^3 + (3+6*k*c)*x^2 - 6*c*x + 7*c^2

lemma hasDerivAt_NN (k c x : ℝ) :
    HasDerivAt (NN k c) (12*k^2*x^3 - 18*k*x^2 + 2*(3+6*k*c)*x - 6*c) x := by
  have h := (((((hasDerivAt_pow 4 x).const_mul (3*k^2)).sub ((hasDerivAt_pow 3 x).const_mul (6*k))).add
    ((hasDerivAt_pow 2 x).const_mul (3+6*k*c))).sub ((hasDerivAt_id' x).const_mul (6*c))).add_const (7*c^2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · norm_num <;> ring
  · simp only [NN, Pi.add_apply, Pi.sub_apply] <;> ring

lemma mfr_eq (k c w u qR x T : ℝ) (hT : u*T = u - c - k*u^2) :
    mfrPayoff k c ⟨w, u, qR, x⟩ = (w - k*u^2)*qR + u*(T - qR - x)*x := by
  simp only [mfrPayoff]; linear_combination (-x) * hT

lemma direct_eq {k c : ℝ} {σ : Profile} (h3 : Stage3Optimal k c σ) {w u qR T : ℝ}
    (hu : 0 < u) (hq : 0 ≤ qR) (hT : u*T = u - c - k*u^2) :
    σ.direct w u qR = max 0 ((T - qR)/2) := by
  obtain ⟨hD0, hopt⟩ := h3 w u qR hu hq
  have hD : mfrPayoff k c (σ.outcomeAtDirect w u qR)
      = (w - k*u^2)*qR + u*(T - qR - σ.direct w u qR)*σ.direct w u qR :=
    mfr_eq k c w u qR _ T hT
  simp only [hD] at hopt
  generalize σ.direct w u qR = D at hD0 hopt ⊢
  rcases le_or_gt 0 (T - qR) with h | h
  · have h1 := hopt ((T-qR)/2) (by linarith)
    rw [mfr_eq k c w u qR _ T hT] at h1
    have h2 : u * (D - (T-qR)/2)^2 ≤ 0 := by nlinarith
    have h3' : (D - (T-qR)/2)^2 ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hu hc]
    have : D = (T-qR)/2 := by nlinarith [sq_nonneg (D - (T-qR)/2)]
    rw [this, max_eq_right (by linarith)]
  · have h1 := hopt 0 le_rfl
    rw [mfr_eq k c w u qR _ T hT] at h1
    rw [max_eq_left (by linarith)]
    by_contra hne
    have hpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hne)
    nlinarith [mul_pos (mul_pos hu hpos) hpos, mul_pos (mul_pos hu hpos) (by linarith : (0:ℝ) < -(T-qR))]

lemma dev_enc {k c : ℝ} {σ : Profile} (h3 : Stage3Optimal k c σ) (h2 : Stage2Optimal σ)
    {u T q : ℝ} (hu : 0 < u) (hT : u*T = u - c - k*u^2) (hq : 0 ≤ q) (hqT : q < T) :
    mfrPayoff k c (σ.outcomeAtOrder (u*(1 - T/2) - u*q) u) = u*T^2/4 + c*q - 3*u*q^2/4 := by
  obtain ⟨hx0, hopt⟩ := h2 (u*(1 - T/2) - u*q) u hu
  have hRq := hopt q hq
  simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, retailerPayoff] at hRq hx0 ⊢
  rw [direct_eq h3 hu hq hT, max_eq_right (by linarith)] at hRq
  have hx : σ.order (u*(1 - T/2) - u*q) u = q := by
    generalize σ.order (u*(1 - T/2) - u*q) u = x at hx0 hRq
    rw [direct_eq h3 hu hx0 hT] at hRq
    rcases lt_or_ge x T with hxT | hxT
    · rw [max_eq_right (by linarith)] at hRq
      have h4 : u*(x - q)^2 ≤ 0 := by nlinarith
      have h5 : (x-q)^2 ≤ 0 := by
        by_contra hc
        push Not at hc
        nlinarith [mul_pos hu hc]
      nlinarith [sq_nonneg (x-q)]
    · rw [max_eq_left (by linarith)] at hRq
      nlinarith [mul_pos hu (pow_pos (sub_pos.2 hqT) 2),
        mul_nonneg hu.le (mul_nonneg (sub_nonneg.2 hxT) (by linarith : (0:ℝ) ≤ x + T/2 - q))]
  rw [hx, direct_eq h3 hu hq hT, max_eq_right (by linarith)]
  simp only [mfrPayoff]
  linear_combination (-(q + (T-q)/2)) * hT

lemma dev_det {k c : ℝ} {σ : Profile} (h3 : Stage3Optimal k c σ) (h2 : Stage2Optimal σ)
    {u T : ℝ} (hu : 0 < u) (hT : u*T = u - c - k*u^2) (hT0 : 0 < T) :
    mfrPayoff k c (σ.outcomeAtOrder (u*(1 - 3*T/2)) u) = (u*(1 - 3*T/2) - k*u^2)*T := by
  obtain ⟨hx0, hopt⟩ := h2 (u*(1 - 3*T/2)) u hu
  have hRT := hopt T hT0.le
  simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, retailerPayoff] at hRT hx0 ⊢
  rw [direct_eq h3 hu hT0.le hT, show (T - T)/2 = 0 by ring, max_self] at hRT
  have hx : σ.order (u*(1 - 3*T/2)) u = T := by
    generalize σ.order (u*(1 - 3*T/2)) u = x at hx0 hRT
    rw [direct_eq h3 hu hx0 hT] at hRT
    rcases lt_or_ge x T with hxT | hxT
    · rw [max_eq_right (by linarith)] at hRT
      nlinarith [mul_pos hu (pow_pos (sub_pos.2 hxT) 2)]
    · rw [max_eq_left (by linarith)] at hRT
      by_contra hne
      have hgt : T < x := lt_of_le_of_ne hxT (Ne.symm hne)
      nlinarith [mul_pos hu (mul_pos (sub_pos.2 hgt) (by linarith : (0:ℝ) < x - T/2))]
  rw [hx, direct_eq h3 hu hT0.le hT, show (T - T)/2 = 0 by ring, max_self]
  simp only [mfrPayoff]
  ring

end QE38

set_option maxHeartbeats 1000000 in
open QE38 in
open QualityEncroach.Uniform in
theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c σ) (henc : 0 < σ.path.qM) :
    1 / (54 * k) < mfrPayoff k c σ.path ∧ retailerPayoff σ.path < 1 / (108 * k) := by
  obtain ⟨h3, h2, hu0, h1⟩ := hσ
  obtain ⟨T, hT⟩ : ∃ T, σ.u * T = σ.u - c - k*σ.u^2 :=
    ⟨(σ.u - c - k*σ.u^2)/σ.u, by field_simp⟩
  obtain ⟨hq0, hRopt⟩ := h2 σ.w σ.u hu0
  have hD := direct_eq h3 (w := σ.w) hu0 hq0 hT
  have henc' : 0 < σ.direct σ.w σ.u (σ.order σ.w σ.u) := henc
  rw [hD] at henc'
  have hqT : σ.order σ.w σ.u < T := by
    rcases lt_max_iff.1 henc' with h | h
    · exact absurd h (lt_irrefl 0)
    · linarith
  have hD' : σ.direct σ.w σ.u (σ.order σ.w σ.u) = (T - σ.order σ.w σ.u)/2 := by
    rw [hD, max_eq_right (by linarith)]
  -- name the path order
  generalize hqdef : σ.order σ.w σ.u = q at hq0 hqT hD' hRopt
  -- retailer step
  obtain ⟨e, he⟩ : ∃ e, e = σ.u*(1 - T/2) - σ.w - σ.u*q := ⟨_, rfl⟩
  have hret : ∀ x, 0 ≤ x → x < T → (e + σ.u*q)*x - (σ.u/2)*x^2 ≤ (e + σ.u*q)*q - (σ.u/2)*q^2 := by
    intro x hx hxT
    have h := hRopt x hx
    simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, retailerPayoff] at h
    rw [hqdef, hD', direct_eq h3 hu0 hx hT, max_eq_right (by linarith)] at h
    rw [he]; nlinarith [h]
  obtain ⟨hr1, hr2⟩ := quad_max (e + σ.u*q) (σ.u/2) q T (by linarith) hq0 hqT hret
  have heq : e*q = 0 := by
    rcases eq_or_lt_of_le hq0 with h | h
    · rw [← h]; ring
    · have := hr2 h
      have : e = 0 := by linarith
      rw [this]; ring
  -- path values
  have hM : mfrPayoff k c σ.path = σ.u*T^2/4 + c*q - 3*σ.u*q^2/4 := by
    show mfrPayoff k c ⟨σ.w, σ.u, σ.order σ.w σ.u, σ.direct σ.w σ.u (σ.order σ.w σ.u)⟩ = _
    rw [hqdef, hD']
    simp only [mfrPayoff]
    linear_combination q * he - (q + (T-q)/2) * hT - heq
  have hR : retailerPayoff σ.path = σ.u*q^2/2 := by
    show retailerPayoff ⟨σ.w, σ.u, σ.order σ.w σ.u, σ.direct σ.w σ.u (σ.order σ.w σ.u)⟩ = _
    rw [hqdef, hD']
    simp only [retailerPayoff]
    linear_combination heq - q * he
  rw [hM, hR]
  rw [hM] at h1
  -- manufacturer's choice of the retailer's quantity
  have hmq : ∀ x, 0 ≤ x → x < T → c*x - (3*σ.u/4)*x^2 ≤ c*q - (3*σ.u/4)*q^2 := by
    intro x hx hxT
    have h := h1 (σ.u*(1 - T/2) - σ.u*x) σ.u hu0
    rw [dev_enc h3 h2 hu0 hT hx hxT] at h
    nlinarith [h]
  obtain ⟨hm1, hm2⟩ := quad_max c (3*σ.u/4) q T (by linarith) hq0 hqT hmq
  have hq_eq : 3*σ.u*q = 2*c := by
    rcases eq_or_lt_of_le hq0 with h | h
    · rw [← h] at hm1 ⊢; linarith
    · have := hm2 h; linarith
  have hreg : 5*c < 3*σ.u - 3*k*σ.u^2 := by
    nlinarith [mul_lt_mul_of_pos_left hqT hu0]
  obtain ⟨M, hMdef⟩ : ∃ M, M = σ.u*T^2/4 + c*q - 3*σ.u*q^2/4 := ⟨_, rfl⟩
  rw [← hMdef] at h1 ⊢
  have hMN : 12*σ.u*M = NN k c σ.u := by
    have hsqT : (σ.u*T)^2 = (σ.u - c - k*σ.u^2)^2 := by rw [hT]
    have hsq3 : (3*σ.u*q)^2 = (2*c)^2 := by rw [hq_eq]
    rw [hMdef]; simp only [NN]
    linear_combination 3 * hsqT + 4 * c * hq_eq - hsq3
  -- encroachment deviations at any quality in the region
  have hdevR : ∀ x, 0 < x → 5*c < 3*x - 3*k*x^2 → NN k c x ≤ 12*x*M := by
    intro x hx hxr
    have hTx : x * ((x - c - k*x^2)/x) = x - c - k*x^2 := by field_simp
    have hq0' : 0 ≤ 2*c/(3*x) := by positivity
    have hqT' : 2*c/(3*x) < (x - c - k*x^2)/x := by
      rw [div_lt_div_iff₀ (by positivity) hx]
      nlinarith [mul_lt_mul_of_pos_right hxr hx]
    have hv := dev_enc h3 h2 hx hTx hq0' hqT'
    have hle := h1 (x*(1 - ((x - c - k*x^2)/x)/2) - x*(2*c/(3*x))) x hx
    rw [hv] at hle
    have e : 12*x*(x*((x - c - k*x^2)/x)^2/4 + c*(2*c/(3*x)) - 3*x*(2*c/(3*x))^2/4) = NN k c x := by
      simp only [NN]; field_simp; ring
    rw [← e]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  -- deterrence deviations
  have hdevZ : ∀ x T', 0 < x → x*T' = x - c - k*x^2 → 0 < T' → (x*(1 - 3*T'/2) - k*x^2)*T' ≤ M := by
    intro x T' hx hT' hT0
    have := dev_det h3 h2 hx hT' hT0
    rw [← this]
    exact h1 _ _ hx
  have hZs : ∀ r, 0 < r → 0 < 1 - k*c/r - r → r*(1 - 3*(1 - k*c/r - r)/2 - r)*(1 - k*c/r - r) ≤ k*M := by
    intro r hr hT0
    have hT' : (r/k)*(1 - k*c/r - r) = r/k - c - k*(r/k)^2 := by field_simp <;> ring
    have h := hdevZ (r/k) (1 - k*c/r - r) (by positivity) hT' hT0
    have e : k*((r/k)*(1 - 3*(1 - k*c/r - r)/2) - k*(r/k)^2)*(1 - k*c/r - r)
        = r*(1 - 3*(1 - k*c/r - r)/2 - r)*(1 - k*c/r - r) := by field_simp <;> ring
    rw [← e, mul_assoc]
    exact mul_le_mul_of_nonneg_left h hk.le
  -- first-order condition
  have hderiv : HasDerivAt (fun x => σ.u * NN k c x - x * NN k c σ.u)
      (σ.u * (12*k^2*σ.u^3 - 18*k*σ.u^2 + 2*(3+6*k*c)*σ.u - 6*c) - 1 * NN k c σ.u) σ.u :=
    ((hasDerivAt_NN k c σ.u).const_mul σ.u).sub ((hasDerivAt_id' σ.u).mul_const (NN k c σ.u))
  have hmax : IsLocalMax (fun x => σ.u * NN k c x - x * NN k c σ.u) σ.u := by
    have hopen : IsOpen ({x : ℝ | 0 < x} ∩ {x : ℝ | 5*c < 3*x - 3*k*x^2}) :=
      IsOpen.inter (isOpen_lt continuous_const continuous_id)
        (isOpen_lt continuous_const (show Continuous (fun x : ℝ => 3*x - 3*k*x^2) by fun_prop))
    refine Filter.eventually_of_mem (hopen.mem_nhds ⟨hu0, hreg⟩) ?_
    intro x hx
    show σ.u * NN k c x - x * NN k c σ.u ≤ σ.u * NN k c σ.u - σ.u * NN k c σ.u
    have h := hdevR x hx.1 hx.2
    rw [← hMN]
    nlinarith [mul_le_mul_of_nonneg_left h hu0.le]
  have hfoc0 := hmax.hasDerivAt_eq_zero hderiv
  have hFOC : 9*k^2*σ.u^4 - 12*k*σ.u^3 + (3+6*k*c)*σ.u^2 - 7*c^2 = 0 := by
    simp only [NN] at hfoc0; linear_combination hfoc0
  -- scaled variables
  have hv : 0 < k*σ.u := mul_pos hk hu0
  have hd : 0 ≤ k*c := mul_nonneg hk.le hc
  have hreg_s : 5*(k*c) < 3*(k*σ.u) - 3*(k*σ.u)^2 := by nlinarith [mul_lt_mul_of_pos_left hreg hk]
  have hd3 : k*c < 3/20 := by nlinarith [sq_nonneg (k*σ.u - 1/2)]
  have hfoc_s : 9*(k*σ.u)^4 - 12*(k*σ.u)^3 + (3+6*(k*c))*(k*σ.u)^2 - 7*(k*c)^2 = 0 := by
    linear_combination k^2 * hFOC
  have hm_s : 12*(k*σ.u)*(k*M) = 3*(k*σ.u)^4 - 6*(k*σ.u)^3 + (3+6*(k*c))*(k*σ.u)^2 - 6*(k*c)*(k*σ.u) + 7*(k*c)^2 := by
    simp only [NN] at hMN; linear_combination k^2 * hMN
  have h13 : 15*(k*c) < 2 → 1/27 - (k*c)/3 + 7*(k*c)^2/4 ≤ k*M := by
    intro h15
    have hx : (0:ℝ) < 1/(3*k) := by positivity
    have hxr : 5*c < 3*(1/(3*k)) - 3*k*(1/(3*k))^2 := by
      have e : 3*(1/(3*k)) - 3*k*(1/(3*k))^2 = 2/(3*k) := by field_simp; ring
      rw [e, lt_div_iff₀ (by positivity)]; linarith
    have h := hdevR _ hx hxr
    have e1 : NN k c (1/(3*k)) = (4/k^2)*(1/27 - (k*c)/3 + 7*(k*c)^2/4) := by
      simp only [NN]; field_simp; ring
    have e2 : 12*(1/(3*k))*M = (4/k^2)*(k*M) := by field_simp; ring
    rw [e1, e2] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have hz21 := hZs (21/100) (by norm_num) (by
    have : k*c/(21/100) = 100*(k*c)/21 := by ring
    rw [this]; linarith)
  have hz3 := hZs (1/3) (by norm_num) (by
    have : k*c/(1/3) = 3*(k*c) := by ring
    rw [this]; linarith)
  obtain ⟨hA, hB⟩ := final_alg (k*c) (k*σ.u) (k*M) hv hd hreg_s hfoc_s hm_s h13 hz21 hz3
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    have hsq3 : (3*σ.u*q)^2 = (2*c)^2 := by rw [hq_eq]
    have key : (σ.u*q^2/2*(108*k))*(k*σ.u) = 24*(k*c)^2 := by
      linear_combination 6*k^2 * hsq3
    have : (σ.u*q^2/2*(108*k))*(k*σ.u) < 1*(k*σ.u) := by rw [key]; linarith
    exact lt_of_mul_lt_mul_right this hv.le
