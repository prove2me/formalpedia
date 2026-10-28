-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.qubitObjectiveTwo_closedForm_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:42:30.998749+00:00
-- url     : https://prove2.me/submissions/dc5a82dc-93d3-40f6-a7ca-5cafdc40101f

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open Real Set


theorem p40_mob_convex (p q u v : ℝ) (hD : ∀ t ∈ Icc (-1:ℝ) 1, 0 < u + v*t)
    (hc : 0 ≤ v*(p*v - q*u)) :
    ConvexOn ℝ (Icc (-1:ℝ) 1) (fun t => (p+q*t)/(u+v*t)) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ1 θ2 h1 h2 hs => ?_⟩
  have hz : θ1 • x + θ2 • y ∈ Icc (-1:ℝ) 1 := (convex_Icc _ _) hx hy h1 h2 hs
  simp only [smul_eq_mul] at hz ⊢
  have Dx := hD x hx
  have Dy := hD y hy
  have Dz := hD _ hz
  have h2' : θ2 = 1 - θ1 := by linarith
  subst h2'
  have key : θ1 * ((p + q * x) / (u + v * x)) + (1-θ1) * ((p + q * y) / (u + v * y))
      - (p + q * (θ1 * x + (1-θ1) * y)) / (u + v * (θ1 * x + (1-θ1) * y))
      = θ1*(1-θ1)*(v*(p*v-q*u))*(y-x)^2/((u+v*x)*(u+v*y)*(u + v * (θ1 * x + (1-θ1) * y))) := by
    have e1 := Dx.ne'; have e2 := Dy.ne'; have e3 := Dz.ne'
    rw [mul_div_assoc', mul_div_assoc', div_add_div _ _ e1 e2, div_sub_div _ _ (mul_ne_zero e1 e2) e3, div_eq_div_iff
      (mul_ne_zero (mul_ne_zero e1 e2) e3) (mul_ne_zero (mul_ne_zero e1 e2) e3)]
    ring
  have : 0 ≤ θ1*(1-θ1)*(v*(p*v-q*u))*(y-x)^2/((u+v*x)*(u+v*y)*(u + v * (θ1 * x + (1-θ1) * y))) := by
    apply div_nonneg
    · have := mul_nonneg (mul_nonneg h1 h2) hc
      exact mul_nonneg this (sq_nonneg _)
    · positivity
  linarith

theorem p40_int_key (r c : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ s in (0:ℝ)..1, (r^2*s - c)/(1 - r^2*s^2)
      = -log (1 - r^2)/2 - c*(log (1+r) - log (1-r))/(2*r) := by
  have hpos : ∀ s ∈ uIcc (0:ℝ) 1, 0 < 1 - r*s ∧ 0 < 1 + r*s ∧ 0 < 1 - r^2*s^2 := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    obtain ⟨h0, h1⟩ := hs
    have : r*s < 1 := by nlinarith
    have : 0 ≤ r*s := by positivity
    refine ⟨by linarith, by linarith, by nlinarith⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => -log (1 - r^2*s^2)/2 - c*(log (1+r*s) - log (1-r*s))/(2*r))
    (f' := fun s => (r^2*s - c)/(1 - r^2*s^2)) (a := 0) (b := 1) ?_ ?_
  · rw [this]; simp
  · intro s hs
    obtain ⟨h1, h2, h3⟩ := hpos s hs
    have d1 : HasDerivAt (fun s => 1 - r^2*s^2) (-(r^2*(2*s))) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (r^2)).const_sub 1
      refine this.congr_deriv ?_
      norm_num
    have d2 : HasDerivAt (fun s => 1 + r*s) r s := by
      simpa using ((hasDerivAt_id s).const_mul r).const_add 1
    have d3 : HasDerivAt (fun s => 1 - r*s) (-r) s := by
      simpa using ((hasDerivAt_id s).const_mul r).const_sub 1
    have := (((d1.log h3.ne').neg.div_const 2).sub
      (((d2.log h2.ne').sub (d3.log h1.ne')).const_mul c |>.div_const (2*r)))
    refine this.congr_deriv ?_
    · have e : 1 - r^2*s^2 = (1+r*s)*(1-r*s) := by ring
      rw [e]; field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs; exact (hpos s hs).2.2.ne'

theorem p40_int_inv (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ s in (0:ℝ)..1, 1/(1 - r^2*s^2) = (log (1+r) - log (1-r))/(2*r) := by
  have hpos : ∀ s ∈ uIcc (0:ℝ) 1, 0 < 1 - r*s ∧ 0 < 1 + r*s ∧ 0 < 1 - r^2*s^2 := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    obtain ⟨h0, h1⟩ := hs
    have : r*s < 1 := by nlinarith
    have : 0 ≤ r*s := by positivity
    refine ⟨by linarith, by linarith, by nlinarith⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => (log (1+r*s) - log (1-r*s))/(2*r))
    (f' := fun s => 1/(1 - r^2*s^2)) (a := 0) (b := 1) ?_ ?_
  · rw [this]; simp
  · intro s hs
    obtain ⟨h1, h2, h3⟩ := hpos s hs
    have d2 : HasDerivAt (fun s => 1 + r*s) r s := by
      simpa using ((hasDerivAt_id s).const_mul r).const_add 1
    have d3 : HasDerivAt (fun s => 1 - r*s) (-r) s := by
      simpa using ((hasDerivAt_id s).const_mul r).const_sub 1
    have := ((d2.log h2.ne').sub (d3.log h1.ne')).div_const (2*r)
    refine this.congr_deriv ?_
    have e : 1 - r^2*s^2 = (1+r*s)*(1-r*s) := by ring
    rw [e]; field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs; exact (hpos s hs).2.2.ne'

theorem p40_h_deriv (r : ℝ) (hr0 : -1 < r) (hr1 : r < 1) :
    HasDerivAt (fun r : ℝ => (1+r)/2 * log ((1+r)/2) + (1-r)/2 * log ((1-r)/2))
      ((log (1+r) - log (1-r))/2) r := by
  have p1 : 0 < (1+r)/2 := by linarith
  have p2 : 0 < (1-r)/2 := by linarith
  have d1 : HasDerivAt (fun r : ℝ => (1+r)/2) (1/2) r := by
    simpa using ((hasDerivAt_id r).const_add 1).div_const 2
  have d2 : HasDerivAt (fun r : ℝ => (1-r)/2) (-(1/2)) r := by
    simpa [neg_div] using ((hasDerivAt_id r).const_sub 1).div_const 2
  have := (d1.mul (d1.log p1.ne')).add (d2.mul (d2.log p2.ne'))
  refine this.congr_deriv ?_
  rw [log_div (by linarith) (by norm_num), log_div (by linarith) (by norm_num)]
  have : 1 + r ≠ 0 := by linarith
  have : 1 - r ≠ 0 := by linarith
  field_simp
  ring

theorem p40_F_convex0 :
    ConvexOn ℝ (Icc (0:ℝ) 1) (fun a : ℝ => (1+√a)/2 * log ((1+√a)/2) + (1-√a)/2 * log ((1-√a)/2)) := by
  have hd : ∀ a ∈ Ioo (0:ℝ) 1, HasDerivAt
      (fun a : ℝ => (1+√a)/2 * log ((1+√a)/2) + (1-√a)/2 * log ((1-√a)/2))
      (∫ s in (0:ℝ)..1, 1/(1 - a*s^2) / 2) a := by
    intro a ha
    have hs0 : 0 < √a := Real.sqrt_pos.2 ha.1
    have hs1 : √a < 1 := by
      rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt ha.1.le ha.2
    have := (p40_h_deriv (√a) (by linarith) hs1).comp a (Real.hasDerivAt_sqrt ha.1.ne')
    refine this.congr_deriv ?_
    rw [intervalIntegral.integral_div]
    have := p40_int_inv (√a) hs0 hs1
    rw [Real.sq_sqrt ha.1.le] at this
    rw [this]
    field_simp
  refine MonotoneOn.convexOn_of_deriv (convex_Icc _ _) ?_ ?_ ?_
  · apply Continuous.continuousOn
    exact (Real.continuous_mul_log.comp (by fun_prop : Continuous fun a : ℝ => (1+√a)/2)).add
      (Real.continuous_mul_log.comp (by fun_prop : Continuous fun a : ℝ => (1-√a)/2))
  · rw [interior_Icc]; intro a ha; exact (hd a ha).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha b hb hab
    rw [(hd a ha).deriv, (hd b hb).deriv]
    have pos : ∀ c ∈ Ioo (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, 0 < 1 - c*s^2 := by
      intro c hc s hs
      have : s^2 ≤ 1 := by nlinarith [hs.1, hs.2]
      nlinarith [hc.1, hc.2]
    have ii : ∀ c ∈ Ioo (0:ℝ) 1, IntervalIntegrable (fun s : ℝ => 1/(1 - c*s^2) / 2)
        MeasureTheory.volume 0 1 := by
      intro c hc
      apply ContinuousOn.intervalIntegrable
      refine (ContinuousOn.div continuousOn_const (by fun_prop) ?_).div_const _
      intro s hs; rw [uIcc_of_le zero_le_one] at hs; exact (pos c hc s hs).ne'
    apply intervalIntegral.integral_mono_on zero_le_one (ii a ha) (ii b hb)
    intro s hs
    have h1 := pos a ha s hs
    have h2 := pos b hb s hs
    have : 1/(1 - a*s^2) ≤ 1/(1 - b*s^2) := by
      apply one_div_le_one_div_of_le h2
      nlinarith [sq_nonneg s]
    linarith

noncomputable def p40F (a : ℝ) : ℝ := (1+√a)/2 * log ((1+√a)/2) + (1-√a)/2 * log ((1-√a)/2)

theorem p40_F_convex : ConvexOn ℝ (Icc (0:ℝ) 1) p40F := p40_F_convex0

theorem p40_ident_core (a b c : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hbc : b = 0 → c = 0) :
    (1+√a)/2 * log ((1+√a)/2) + (1-√a)/2 * log ((1-√a)/2) -
      ((1 + c/√b)/2 * log ((1+√b)/2) + (1 - c/√b)/2 * log ((1-√b)/2))
      = p40F a + log 2 + ∫ s in (0:ℝ)..1, (b*s - c)/(1 - b*s^2) := by
  rcases hb0.eq_or_lt with h | h
  · subst h
    rw [hbc rfl]
    simp [p40F]
    ring
  · obtain ⟨r, hr0, rfl⟩ : ∃ r, 0 < r ∧ b = r^2 := ⟨√b, Real.sqrt_pos.2 h, (Real.sq_sqrt h.le).symm⟩
    have hr1 : r < 1 := by nlinarith
    rw [p40_int_key r c hr0 hr1, Real.sqrt_sq hr0.le, p40F]
    rw [show log ((1+r)/2) = log (1+r) - log 2 from log_div (by linarith) (by norm_num),
      show log ((1-r)/2) = log (1-r) - log 2 from log_div (by linarith) (by norm_num),
      show 1 - r^2 = (1-r)*(1+r) by ring, log_mul (by linarith) (by linarith)]
    field_simp
    ring

theorem p40_int_convex (R : ℝ → ℝ → ℝ) (hR : ∀ s ∈ Icc (0:ℝ) 1, ConvexOn ℝ (Icc (-1:ℝ) 1) (R s))
    (hI : ∀ t ∈ Icc (-1:ℝ) 1, IntervalIntegrable (fun s => R s t) MeasureTheory.volume 0 1) :
    ConvexOn ℝ (Icc (-1:ℝ) 1) (fun t => ∫ s in (0:ℝ)..1, R s t) := by
  refine ⟨convex_Icc _ _, fun x hx y hy θ1 θ2 h1 h2 hsum => ?_⟩
  have hz : θ1 • x + θ2 • y ∈ Icc (-1:ℝ) 1 := (convex_Icc _ _) hx hy h1 h2 hsum
  simp only [smul_eq_mul] at hz ⊢
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((hI x hx).const_mul _) ((hI y hy).const_mul _)]
  apply intervalIntegral.integral_mono_on zero_le_one (hI _ hz)
    (((hI x hx).const_mul _).add ((hI y hy).const_mul _))
  intro s hs
  have := (hR s hs).2 hx hy h1 h2 hsum
  simpa only [smul_eq_mul] using this

theorem solution (beta T : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : beta < T ∧ T ≤ 1 - beta) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t : ℝ =>
      let x := beta - T + (1 - beta - T) * t
      let y2 := (1 - beta - T) ^ 2 * (1 - t ^ 2)
      let rs := Real.sqrt (x ^ 2 + y2)
      let rr := Real.sqrt ((x + 2 * T) ^ 2 + y2)
      let w := ((x + 2 * T) * x + y2) / rs
      (1 + rr) / 2 * Real.log ((1 + rr) / 2) + (1 - rr) / 2 * Real.log ((1 - rr) / 2) -
        ((1 + w) / 2 * Real.log ((1 + rs) / 2) + (1 - w) / 2 * Real.log ((1 - rs) / 2))) := by
  obtain ⟨hb0, hbh⟩ := hbeta
  obtain ⟨hTb, hT1⟩ := hT
  have hη : 0 ≤ 1 - beta - T := by linarith
  -- affine data
  have hA : ∀ t ∈ Icc (-1:ℝ) 1, 0 ≤ (beta+T)^2 + (1-beta-T)^2 + 2*(beta+T)*(1-beta-T)*t ∧
      (beta+T)^2 + (1-beta-T)^2 + 2*(beta+T)*(1-beta-T)*t ≤ 1 := by
    intro t ht
    have h1 : 0 ≤ 2*(beta+T)*(1-beta-T) := mul_nonneg (by linarith) hη
    constructor
    · nlinarith [mul_nonneg h1 (show 0 ≤ t + 1 by linarith [ht.1]), sq_nonneg (beta+T-(1-beta-T))]
    · nlinarith [mul_nonneg h1 (show 0 ≤ 1 - t by linarith [ht.2])]
  have hB : ∀ t ∈ Icc (-1:ℝ) 1, 0 ≤ (beta-T)^2 + (1-beta-T)^2 + 2*(beta-T)*(1-beta-T)*t ∧
      (beta-T)^2 + (1-beta-T)^2 + 2*(beta-T)*(1-beta-T)*t < 1 := by
    intro t ht
    have h1 : 0 ≤ 2*(T-beta)*(1-beta-T) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hη
    constructor
    · nlinarith [mul_nonneg h1 (show 0 ≤ 1 - t by linarith [ht.2]), sq_nonneg (beta-T+(1-beta-T))]
    · nlinarith [mul_nonneg h1 (show 0 ≤ t + 1 by linarith [ht.1])]
  -- F part
  have hFa : ConvexOn ℝ (Icc (-1:ℝ) 1)
      (fun t => p40F ((beta+T)^2 + (1-beta-T)^2 + 2*(beta+T)*(1-beta-T)*t)) := by
    refine ⟨convex_Icc _ _, fun x hx y hy θ1 θ2 h1 h2 hs => ?_⟩
    have := p40_F_convex.2 (hA x hx) (hA y hy) h1 h2 hs
    simp only [smul_eq_mul] at this ⊢
    convert this using 2
    have : θ2 = 1 - θ1 := by linarith
    subst this; ring
  -- integral part
  set b0 := (beta-T)^2 + (1-beta-T)^2 with hb0def
  set b1 := 2*(beta-T)*(1-beta-T) with hb1def
  set c0 := b0 + 2*T*(beta-T) with hc0def
  set c1 := b1 + 2*T*(1-beta-T) with hc1def
  have hRc : ∀ s ∈ Icc (0:ℝ) 1, ConvexOn ℝ (Icc (-1:ℝ) 1)
      (fun t => ((b0*s - c0) + (b1*s - c1)*t)/((1 - s^2*b0) + (-(s^2*b1))*t)) := by
    intro s hs
    apply p40_mob_convex
    · intro t ht
      obtain ⟨h1, h2⟩ := hB t ht
      have : s^2 ≤ 1 := by nlinarith [hs.1, hs.2]
      nlinarith [mul_nonneg (sq_nonneg s) h1]
    · have hv : 0 ≤ -(s^2*b1) := by
        have : 0 ≤ T - beta := by linarith
        have : 0 ≤ s^2*(2*(T-beta)*(1-beta-T)) :=
          mul_nonneg (sq_nonneg s) (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hη)
        rw [hb1def]; nlinarith
      have hE : 0 ≤ (beta-T)*(1-s) + T + s^2*T*((beta-T)^2-(1-beta-T)^2) := by
        obtain ⟨hs0, hs1⟩ := hs
        rcases le_total ((1-beta-T)^2) ((beta-T)^2) with h | h
        · have : 0 ≤ s^2*T*((beta-T)^2-(1-beta-T)^2) := by
            apply mul_nonneg (mul_nonneg (sq_nonneg s) (by linarith)) (by linarith)
          nlinarith
        · have e : (beta-T)*(1-s) + T + s^2*T*((beta-T)^2-(1-beta-T)^2)
              = (1-s)*beta + s*(T*(1+(beta-T)^2-(1-beta-T)^2)) + T*((1-beta-T)^2-(beta-T)^2)*(s*(1-s)) := by ring
          rw [e]
          have hη1 : (1-beta-T)^2 ≤ 1 := by nlinarith
          have : 0 ≤ T*(1+(beta-T)^2-(1-beta-T)^2) := mul_nonneg (by linarith) (by nlinarith [sq_nonneg (beta-T)])
          have : 0 ≤ T*((1-beta-T)^2-(beta-T)^2)*(s*(1-s)) :=
            mul_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hs0 (by linarith))
          have : 0 ≤ (1-s)*beta := mul_nonneg (by linarith) hb0.le
          have : 0 ≤ s*(T*(1+(beta-T)^2-(1-beta-T)^2)) := mul_nonneg hs0 (by assumption)
          linarith
      have e : ((b0*s - c0))*(-(s^2*b1)) - (b1*s - c1)*(1 - s^2*b0)
          = 2*(1-beta-T)*((beta-T)*(1-s) + T + s^2*T*((beta-T)^2-(1-beta-T)^2)) := by
        rw [hc0def, hc1def, hb0def, hb1def]; ring
      rw [e]
      exact mul_nonneg hv (mul_nonneg (by linarith) hE)
  have hIi : ∀ t ∈ Icc (-1:ℝ) 1, IntervalIntegrable
      (fun s => ((b0*s - c0) + (b1*s - c1)*t)/((1 - s^2*b0) + (-(s^2*b1))*t)) MeasureTheory.volume 0 1 := by
    intro t ht
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    obtain ⟨h1, h2⟩ := hB t ht
    have : s^2 ≤ 1 := by nlinarith [hs.1, hs.2]
    nlinarith [mul_nonneg (sq_nonneg s) h1]
  have hI := p40_int_convex _ hRc hIi
  have hsum := (hFa.add (convexOn_const (Real.log 2) (convex_Icc (-1:ℝ) 1))).add hI
  refine hsum.congr ?_
  intro t ht
  dsimp only
  have hbt := hB t ht
  have key := p40_ident_core ((beta - T + (1 - beta - T) * t + 2*T)^2 + (1 - beta - T) ^ 2 * (1 - t ^ 2))
    ((beta - T + (1 - beta - T) * t)^2 + (1 - beta - T) ^ 2 * (1 - t ^ 2))
    ((beta - T + (1 - beta - T) * t + 2*T)*(beta - T + (1 - beta - T) * t) + (1 - beta - T) ^ 2 * (1 - t ^ 2))
    (by nlinarith [hbt.1]) (by nlinarith [hbt.2]) ?_
  · rw [key]
    simp only [Pi.add_apply]
    rw [show (beta+T)^2 + (1-beta-T)^2 + 2*(beta+T)*(1-beta-T)*t
      = (beta - T + (1 - beta - T) * t + 2 * T) ^ 2 + (1 - beta - T) ^ 2 * (1 - t ^ 2) by ring]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hc0def, hc1def, hb0def, hb1def]
    congr 1 <;> ring
  · intro h0
    have hy : 0 ≤ (1 - beta - T) ^ 2 * (1 - t ^ 2) := by
      have : 0 ≤ 1 - t^2 := by nlinarith [ht.1, ht.2]
      positivity
    have hx : (beta - T + (1 - beta - T) * t)^2 = 0 := by nlinarith [sq_nonneg (beta - T + (1 - beta - T) * t)]
    have hy0 : (1 - beta - T) ^ 2 * (1 - t ^ 2) = 0 := by nlinarith [sq_nonneg (beta - T + (1 - beta - T) * t)]
    have hx0 : beta - T + (1 - beta - T) * t = 0 := by simpa using hx
    rw [hx0, hy0]; ring

end
