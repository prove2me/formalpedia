-- Prove2me | solution 1 for ResolvingNRM.FRLower.q1_probability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:55:10.890196+00:00
-- url     : https://prove2.me/submissions/a58294a5-a3c3-4951-8b42-961bdb84c03c

import Mathlib

open Real Nat

lemma stirling_upper (n : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ √(2 * π * n) * (n / exp 1) ^ n * exp (1 / (12 * n)) := by
  set a : ℕ → ℝ := fun m => Real.log (Stirling.stirlingSeq (m + 1)) - 1 / (12 * ((m:ℝ) + 1))
    with ha
  have hmono : Monotone a := by
    refine monotone_nat_of_le_succ fun m => ?_
    have h := Stirling.log_stirlingSeq_sdiff_le (m + 1)
    simp only [ha]
    push_cast at h ⊢
    have e : (1:ℝ) / (12 * ((m:ℝ) + 1)) - 1 / (12 * ((m:ℝ) + 1 + 1))
        = 1 / (12 * ((m:ℝ) + 1) * ((m:ℝ) + 1 + 1)) := by
      field_simp; ring
    linarith
  have hlim : Filter.Tendsto a Filter.atTop (nhds (Real.log (√π))) := by
    have h1 : Filter.Tendsto (fun m : ℕ => Stirling.stirlingSeq (m + 1)) Filter.atTop
        (nhds (√π)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr Stirling.tendsto_stirlingSeq_sqrt_pi
    have h2 := (Real.continuousAt_log (by positivity : (√π) ≠ 0)).tendsto.comp h1
    have h3 : Filter.Tendsto (fun m : ℕ => 1 / (12 * ((m:ℝ) + 1))) Filter.atTop (nhds 0) := by
      have h4 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/12 : ℝ)
      simp only [mul_zero] at h4
      refine h4.congr fun m => ?_
      field_simp
    have := h2.sub h3
    simpa [ha] using this
  have hle := hmono.ge_of_tendsto hlim (n - 1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, ha] at hle
  have hpos := Stirling.stirlingSeq'_pos m
  have hs : Stirling.stirlingSeq (m + 1) ≤ √π * exp (1 / (12 * ((m:ℝ) + 1))) := by
    have : Real.log (Stirling.stirlingSeq (m + 1)) ≤ Real.log (√π) + 1 / (12 * ((m:ℝ) + 1)) := by
      linarith
    rw [← Real.exp_log hpos, ← Real.exp_log (by positivity : (0:ℝ) < √π), ← Real.exp_add]
    exact Real.exp_le_exp.mpr this
  unfold Stirling.stirlingSeq at hs
  have hd : 0 < √(2 * ((m + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) / exp 1) ^ (m + 1) := by positivity
  rw [div_le_iff₀ hd] at hs
  have hsq : √(2 * π * ((m + 1 : ℕ) : ℝ)) = √π * √(2 * ((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  rw [hsq]
  push_cast at hs ⊢
  nlinarith [hs]

set_option maxHeartbeats 1000000 in
lemma pmf_lower_below (T : ℕ) (k : ℕ) (hs100 : 100 ≤ √(T:ℝ))
    (hk1 : (T:ℝ) - 4 * √(T:ℝ) ≤ k) (hk2 : (k:ℝ) ≤ T) :
    (1 - 110 / √(T:ℝ)) * (ProbabilityTheory.gaussianPDFReal 0 1 (((k:ℝ) - T) / √(T:ℝ)) / √(T:ℝ))
      ≤ ProbabilityTheory.poissonPMFReal (T:ℝ).toNNReal k := by
  set t : ℝ := (T:ℝ) with ht
  set s : ℝ := √t with hs
  set kk : ℝ := (k:ℝ) with hkk
  have hs1 : 1 ≤ s := by linarith
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hss : s * s = t := Real.mul_self_sqrt ht0
  have ht1 : (1:ℝ) ≤ t := by nlinarith
  have hkks : s ≤ kk := by nlinarith
  have hk0 : 1 ≤ kk := by linarith
  have hkpos : 0 < kk := by linarith
  have hk1n : 1 ≤ k := by rw [hkk] at hk0; exact_mod_cast hk0
  have hfac := stirling_upper k hk1n
  rw [← hkk] at hfac
  unfold ProbabilityTheory.poissonPMFReal
  rw [Real.coe_toNNReal _ (by linarith)]
  have step1 : exp (-t) * t ^ k / (√(2 * π * kk) * (kk / exp 1) ^ k * exp (1 / (12 * kk)))
      ≤ exp (-t) * t ^ k / (k ! : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
  refine le_trans ?_ step1
  have hsqrt : √(2 * π * kk) = √(2 * π) * s * exp (Real.log (kk / t) / 2) := by
    have e1 : exp (Real.log (kk / t) / 2) = √(kk / t) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]; ring_nf
    rw [e1, hs, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1; field_simp
  have htk : t ^ k = exp (k * Real.log t) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  have hkk' : (kk / exp 1) ^ k = exp (k * (Real.log kk - 1)) := by
    rw [Real.exp_nat_mul, Real.exp_sub, Real.exp_log hkpos]
  rw [hsqrt, htk, hkk']
  have hR : exp (-t) * exp (k * Real.log t) /
      (√(2 * π) * s * exp (Real.log (kk / t) / 2) * exp (k * (Real.log kk - 1)) *
        exp (1 / (12 * kk))) =
      exp (-t + k * Real.log t - Real.log (kk / t) / 2 - k * (Real.log kk - 1)
        - 1 / (12 * kk)) / (√(2 * π) * s) := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_sub, Real.exp_add]
    field_simp
  rw [hR]
  unfold ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hx2 : ((kk - t) / s) ^ 2 = (kk - t) ^ 2 / t := by
    rw [div_pow, ← hss]; ring
  rw [hx2]
  have hL : (1 - 110 / s) * ((√(2 * π))⁻¹ * exp (-((kk - t) ^ 2 / t) / 2) / s)
      ≤ exp (-110 / s) * exp (-((kk - t) ^ 2 / t) / 2) / (√(2 * π) * s) := by
    have h1 : 1 - 110 / s ≤ exp (-110 / s) := by
      have := Real.add_one_le_exp (-110 / s); linarith [show -110 / s = -(110/s) by ring]
    rw [show (1 - 110 / s) * ((√(2 * π))⁻¹ * exp (-((kk - t) ^ 2 / t) / 2) / s)
        = (1 - 110 / s) * exp (-((kk - t) ^ 2 / t) / 2) / (√(2 * π) * s) by field_simp]
    gcongr
  refine le_trans hL ?_
  rw [← Real.exp_add]
  gcongr
  -- exponent inequality
  set d : ℝ := t - kk with hd
  set x : ℝ := d / t with hx
  have hd0 : 0 ≤ d := by linarith
  have hd4 : d ≤ 4 * s := by linarith
  have htpos : 0 < t := by linarith
  have hx0 : 0 ≤ x := div_nonneg hd0 ht0
  have hx4 : x ≤ 4 / s := by
    rw [hx, div_le_div_iff₀ htpos (by linarith), ← hss]; nlinarith
  have hxs : x ≤ 1 / 25 := by
    have : 4 / s ≤ 4 / 100 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs100
    linarith
  have hkx : kk / t = 1 - x := by rw [hx, hd]; field_simp; ring
  have hlog : Real.log (kk / t) = Real.log kk - Real.log t :=
    Real.log_div (by linarith) (by linarith)
  have habs := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 2
  rw [abs_of_nonneg hx0, show Real.log (1 - x) = Real.log (kk / t) by rw [hkx]] at habs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at habs
  norm_num at habs
  have hLle : Real.log (kk / t) ≤ -x - x ^ 2 / 2 + (21 / 20) * x ^ 3 := by
    have h1 := (abs_le.mp habs).2
    have h2 : x ^ 3 / (1 - x) ≤ (21 / 20) * x ^ 3 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg hx0 3]
    linarith
  have hLnp : Real.log (kk / t) ≤ 0 := by
    apply Real.log_nonpos (by positivity); rw [div_le_one htpos]; exact hk2
  rw [hlog] at hLle hLnp
  set L := Real.log kk - Real.log t with hLdef
  have hA0 : kk * L ≤ kk * (-x - x ^ 2 / 2 + (21 / 20) * x ^ 3) :=
    mul_le_mul_of_nonneg_left hLle hkpos.le
  have hA1 : kk * (-x - x ^ 2 / 2 + (21 / 20) * x ^ 3) =
      -(kk * (x + x ^ 2 / 2)) + (21 / 20) * (kk * x ^ 3) := by ring
  have hkd : kk = t - d := by rw [hd]; ring
  have hId : kk * (x + x ^ 2 / 2) = d - d ^ 2 / (2 * t) - d ^ 3 / (2 * t ^ 2) := by
    rw [hkd, hx]; field_simp; ring
  have hx3 : kk * x ^ 3 ≤ d ^ 3 / t ^ 2 := by
    have : kk * x ^ 3 ≤ t * x ^ 3 := mul_le_mul_of_nonneg_right hk2 (pow_nonneg hx0 3)
    have e : t * x ^ 3 = d ^ 3 / t ^ 2 := by rw [hx]; field_simp
    linarith
  have hd3 : d ^ 3 / t ^ 2 ≤ 64 / s := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    have h3 : d ^ 3 ≤ (4 * s) ^ 3 := by gcongr
    have h4 : (4 * s) ^ 3 * s = 64 * t ^ 2 := by
      have : t ^ 2 = (s * s) ^ 2 := by rw [hss]
      rw [this]; ring
    calc d ^ 3 * s ≤ (4 * s) ^ 3 * s := mul_le_mul_of_nonneg_right h3 (by linarith)
      _ = 64 * t ^ 2 := h4
  have h12 : 1 / (12 * kk) ≤ 1 / s := by
    apply one_div_le_one_div_of_le (by linarith); linarith
  have hsq : -((kk - t) ^ 2 / t) / 2 = -(d ^ 2 / (2 * t)) := by
    rw [hd]; field_simp; ring
  rw [hsq, hlog]
  have e110 : -110 / s = -(110 / s) := by ring
  have hpos2 : 0 ≤ 2.8 / s := by positivity
  have hE : (k:ℝ) * Real.log t - (k:ℝ) * (Real.log kk - 1) = -(kk * L) + kk := by
    show (k:ℝ) * Real.log t - (k:ℝ) * (Real.log (k:ℝ) - 1) =
      -((k:ℝ) * (Real.log (k:ℝ) - Real.log t)) + (k:ℝ)
    ring
  have h3nn : 0 ≤ d ^ 3 / (2 * t ^ 2) := div_nonneg (pow_nonneg hd0 3) (by positivity)
  have h3e : d ^ 3 / (2 * t ^ 2) = (d ^ 3 / t ^ 2) / 2 := by ring
  have i1 : 64 / s = 64 * s⁻¹ := by ring
  have i2 : -110 / s = -110 * s⁻¹ := by ring
  have i3 : 1 / s = s⁻¹ := by ring
  have hdd : -t + kk = -d := by rw [hd]; ring
  rw [i1] at hd3
  rw [i3] at h12
  rw [i2]
  linarith

open MeasureTheory ProbabilityTheory

lemma chord_piece (a b : ℝ) (hab : a < b) (hs : a + b < 0) :
    (exp (-b ^ 2 / 2) - exp (-a ^ 2 / 2)) / (-(a + b) / 2) ≤
      ∫ x in a..b, exp (-x ^ 2 / 2) := by
  set m : ℝ := -(a + b) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hF : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => exp (m * x + a * b / 2) / m)
      (exp (m * x + a * b / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => m * x + a * b / 2) m x := by
      simpa using ((hasDerivAt_id x).const_mul m).add_const (a * b / 2)
    have h2 := (h1.exp).div_const m
    rwa [mul_div_cancel_right₀ _ hm0.ne'] at h2
  have hint : ∫ x in a..b, exp (m * x + a * b / 2) =
      exp (m * b + a * b / 2) / m - exp (m * a + a * b / 2) / m := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    exact (by fun_prop : Continuous fun x => exp (m * x + a * b / 2)).intervalIntegrable _ _
  have e1 : m * b + a * b / 2 = -b ^ 2 / 2 := by rw [hm]; ring
  have e2 : m * a + a * b / 2 = -a ^ 2 / 2 := by rw [hm]; ring
  rw [e1, e2] at hint
  have hle : ∫ x in a..b, exp (m * x + a * b / 2) ≤ ∫ x in a..b, exp (-x ^ 2 / 2) := by
    apply intervalIntegral.integral_mono_on hab.le
    · exact (by fun_prop : Continuous fun x => exp (m * x + a * b / 2)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x : ℝ => exp (-x ^ 2 / 2)).intervalIntegrable _ _
    intro x hx
    apply exp_le_exp.mpr
    rw [hm]
    nlinarith [hx.1, hx.2]
  rw [hint] at hle
  rw [sub_div]
  exact hle

lemma exp_half_le : exp (1 / 2 : ℝ) ≤ 1.6488 := by
  have h : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
    rw [← exp_nat_mul]; norm_num
  have h1 := exp_one_lt_d9
  nlinarith [exp_pos (1/2 : ℝ)]

lemma exp_low (n : ℕ) (f : ℝ) (hf : 0 ≤ f) :
    (2.7182818283 : ℝ) ^ n * (1 + f + f ^ 2 / 2) ≤ exp (n + f) := by
  rw [exp_add, ← exp_one_pow]
  gcongr
  · exact exp_one_gt_d9.le
  · exact quadratic_le_exp_of_nonneg hf

lemma gauss_int_lower : (0.0013 : ℝ) ≤ ∫ x in (-4:ℝ)..(-3), gaussianPDFReal 0 1 x := by
  have hg : ∀ x, gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
    intro x; unfold gaussianPDFReal; simp only [NNReal.coe_one, mul_one, sub_zero]
  simp_rw [hg]
  rw [intervalIntegral.integral_const_mul]
  have hc : Continuous fun x : ℝ => exp (-x ^ 2 / 2) := by fun_prop
  have hsplit : ∫ x in (-4:ℝ)..(-3), exp (-x ^ 2 / 2) =
      (∫ x in (-4:ℝ)..(-3.75), exp (-x ^ 2 / 2)) + (∫ x in (-3.75:ℝ)..(-3.5), exp (-x ^ 2 / 2)) +
      (∫ x in (-3.5:ℝ)..(-3.25), exp (-x ^ 2 / 2)) + (∫ x in (-3.25:ℝ)..(-3), exp (-x ^ 2 / 2)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  have p1 := chord_piece (-4) (-3.75) (by norm_num) (by norm_num)
  have p2 := chord_piece (-3.75) (-3.5) (by norm_num) (by norm_num)
  have p3 := chord_piece (-3.5) (-3.25) (by norm_num) (by norm_num)
  have p4 := chord_piece (-3.25) (-3) (by norm_num) (by norm_num)
  norm_num at p1 p2 p3 p4
  -- numeric exp bounds
  have E3 : (1 : ℝ) / ((2.7182818286 : ℝ) ^ 4 * 1.6488) ≤ exp (-(9 / 2)) := by
    rw [exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (exp_pos _)
    have : exp (9 / 2 : ℝ) = exp 1 ^ 4 * exp (1 / 2) := by
      rw [← exp_nat_mul, ← exp_add]; norm_num
    rw [this]
    have h1 := exp_one_lt_d9
    have h2 := exp_half_le
    gcongr
  have up : ∀ (n : ℕ) (f y : ℝ), 0 ≤ f → y = n + f →
      exp (-y) ≤ 1 / ((2.7182818283 : ℝ) ^ n * (1 + f + f ^ 2 / 2)) := by
    intro n f y hf hy
    rw [exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    rw [hy]; exact exp_low n f hf
  have E325 := up 5 (9/32) (169/32) (by norm_num) (by norm_num)
  have E35 := up 6 (1/8) (49/8) (by norm_num) (by norm_num)
  have E375 := up 7 (1/32) (225/32) (by norm_num) (by norm_num)
  have E4 := up 8 0 8 (by norm_num) (by norm_num)
  have hpi : √(2 * π) ≤ 2.5067 := by
    rw [sqrt_le_left (by norm_num)]
    nlinarith [pi_lt_d4]
  have hsq : 0 < √(2 * π) := by positivity
  rw [hsplit]
  have key : (0.00326 : ℝ) ≤ (∫ x in (-4:ℝ)..(-3.75), exp (-x ^ 2 / 2)) +
      (∫ x in (-3.75:ℝ)..(-3.5), exp (-x ^ 2 / 2)) +
      (∫ x in (-3.5:ℝ)..(-3.25), exp (-x ^ 2 / 2)) + (∫ x in (-3.25:ℝ)..(-3), exp (-x ^ 2 / 2)) := by
    norm_num
    norm_num at E3 E325 E35 E375 E4
    linarith
  have hinv : (1 / 2.5067 : ℝ) ≤ (√(2 * π))⁻¹ := by
    rw [← one_div]; exact one_div_le_one_div_of_le hsq hpi
  nlinarith

lemma gauss_mono {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ 0) :
    gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 y := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  have : y ^ 2 ≤ x ^ 2 := by nlinarith
  linarith

lemma gauss_m3_le : gaussianPDFReal 0 1 (-3) ≤ 0.0074 := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have h1 : (√(2 * π))⁻¹ ≤ 1 / 2.5 := by
    rw [← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_d2]
  have h2 : rexp (-(-3:ℝ) ^ 2 / 2) ≤ 1 / 54.5 := by
    have e : -(-3:ℝ) ^ 2 / 2 = -(4 + 1/2) := by norm_num
    rw [e, Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have : exp (4 + 1/2 : ℝ) = exp 1 ^ 4 * exp (1/2) := by
      rw [← exp_nat_mul, ← exp_add]; norm_num
    rw [this]
    have h3 := exp_one_gt_d9
    have h4 : (1:ℝ) ≤ exp (1/2) := by
      have := Real.add_one_le_exp (1/2 : ℝ); linarith
    have h5 : (2.7182818283:ℝ) ^ 4 ≤ exp 1 ^ 4 := by gcongr
    nlinarith
  calc (√(2 * π))⁻¹ * rexp (-(-3:ℝ) ^ 2 / 2) ≤ (1 / 2.5) * (1 / 54.5) := by
        gcongr
    _ ≤ 0.0074 := by norm_num

theorem solution (T' : ℕ) (hT : 1 ≤ T') :
    (∑' k : ℕ, if (T' : ℝ) - 4 * Real.sqrt (T' : ℝ) ≤ (k : ℝ) ∧
        (k : ℝ) ≤ (T' : ℝ) - 3 * Real.sqrt (T' : ℝ) then
        ProbabilityTheory.poissonPMFReal (T' : ℝ).toNNReal k else (0 : ℝ)) ≥
      0.0013 - 0.9496 / Real.sqrt (T' : ℝ) := by
  set t : ℝ := (T':ℝ) with ht
  set s : ℝ := √t with hs
  set g : ℝ → ℝ := gaussianPDFReal 0 1 with hg
  set G : ℝ := ∫ x in (-4:ℝ)..(-3), g x with hG
  have ht1 : (1:ℝ) ≤ t := by rw [ht]; exact_mod_cast hT
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1
  have hss : s * s = t := Real.mul_self_sqrt (by linarith)
  have hgc : Continuous g := by
    rw [hg]; unfold gaussianPDFReal; fun_prop
  have hg3 : g (-3) ≤ 0.0074 := gauss_m3_le
  have hGlow : 0.0013 ≤ G := gauss_int_lower
  have hG_le : G ≤ g (-3) := by
    have : G ≤ ∫ x in (-4:ℝ)..(-3), g (-3) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hgc.intervalIntegrable _ _)
        intervalIntegrable_const
      intro x hx; exact gauss_mono hx.2 (by norm_num)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hLnn : 0 ≤ ∑' k : ℕ, (if t - 4 * s ≤ (k : ℝ) ∧ (k : ℝ) ≤ t - 3 * s then
        poissonPMFReal t.toNNReal k else (0 : ℝ)) :=
    tsum_nonneg fun k => by split_ifs <;> simp [poissonPMFReal_nonneg]
  rcases lt_or_ge s 730 with hs4 | hs4
  · have : 0.9496 / s ≥ 0.9496 / 730 := div_le_div_of_nonneg_left (by norm_num) (by linarith)
      hs4.le
    show _ ≥ 0.0013 - 0.9496 / s
    linarith
  -- main case
  set a : ℝ := t - 4 * s with ha
  set b : ℝ := t - 3 * s with hb
  set k0 : ℕ := ⌈a⌉₊ with hk0
  set k1 : ℕ := ⌊b⌋₊ with hk1
  have ha1 : 1 ≤ a := by rw [ha, ← hss]; nlinarith
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hk0a : a ≤ (k0:ℝ) := Nat.le_ceil a
  have hk0a' : (k0:ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hk1b : (k1:ℝ) ≤ b := Nat.floor_le hb0
  have hk1b' : b < (k1:ℝ) + 1 := Nat.lt_floor_add_one b
  have hk01 : k0 ≤ k1 := by
    have : (k0:ℝ) < (k1:ℝ) + 1 := by linarith
    have : k0 < k1 + 1 := by exact_mod_cast this
    omega
  have hk0pos : 1 ≤ k0 := by
    have : (1:ℝ) ≤ k0 := by linarith
    exact_mod_cast this
  have hsum : (∑' k : ℕ, (if a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b then
        poissonPMFReal t.toNNReal k else (0 : ℝ))) =
      ∑ k ∈ Finset.Icc k0 k1, poissonPMFReal t.toNNReal k := by
    rw [tsum_eq_sum (s := Finset.Icc k0 k1)]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [if_pos]
      constructor
      · exact Nat.ceil_le.mp hk.1
      · exact (Nat.le_floor_iff hb0).mp hk.2
    · intro k hk
      rw [if_neg]
      intro h
      apply hk
      rw [Finset.mem_Icc]
      exact ⟨Nat.ceil_le.mpr h.1, (Nat.le_floor_iff hb0).mpr h.2⟩
  show _ ≥ 0.0013 - 0.9496 / s
  rw [hsum]
  set f : ℝ → ℝ := fun y => g ((y - t) / s) / s with hf
  have hspos : 0 < s := by linarith
  have hfc : Continuous f := by
    rw [hf]; exact (hgc.comp (by fun_prop)).div_const _
  have hfnn : ∀ y, 0 ≤ f y := fun y => div_nonneg (gaussianPDFReal_nonneg 0 1 _) hspos.le
  have hfmono : MonotoneOn f (Set.Iic t) := by
    intro x hx y hy hxy
    simp only [hf]
    apply div_le_div_of_nonneg_right _ hspos.le
    apply gauss_mono
    · exact div_le_div_of_nonneg_right (by linarith) hspos.le
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith [Set.mem_Iic.mp hy]) hspos.le
  have hcov : ∫ y in a..b, f y = G := by
    have e : ∀ y, f y = s⁻¹ * g (y / s - t / s) := by
      intro y; simp only [hf]; rw [sub_div]; field_simp
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div_sub _
      hspos.ne']
    have e1 : a / s - t / s = -4 := by rw [ha, ← hss]; field_simp; ring
    have e2 : b / s - t / s = -3 := by rw [hb, ← hss]; field_simp; ring
    rw [e1, e2, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hspos.ne', one_mul]
  have hfb : f b = g (-3) / s := by
    simp only [hf]; congr 2; rw [hb]; field_simp; ring
  have hbt : b ≤ t := by linarith
  -- tail piece
  have htail : ∫ y in (k1:ℝ)..b, f y ≤ g (-3) / s := by
    have : ∫ y in (k1:ℝ)..b, f y ≤ ∫ y in (k1:ℝ)..b, f b := by
      apply intervalIntegral.integral_mono_on hk1b (hfc.intervalIntegrable _ _)
        intervalIntegrable_const
      intro x hx
      exact hfmono (Set.mem_Iic.mpr (by linarith [hx.2])) (Set.mem_Iic.mpr hbt) hx.2
    rw [intervalIntegral.integral_const, smul_eq_mul, hfb] at this
    have h6 : 0 ≤ g (-3) / s := div_nonneg (gaussianPDFReal_nonneg 0 1 _) hspos.le
    nlinarith
  have hsplit1 : ∫ y in a..b, f y = (∫ y in a..(k1:ℝ), f y) + ∫ y in (k1:ℝ)..b, f y :=
    (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)).symm
  have hcast : (((k0 - 1 : ℕ) : ℝ)) = (k0:ℝ) - 1 := by
    rw [Nat.cast_sub hk0pos]; simp
  have hsplit2 : ∫ y in (((k0 - 1 : ℕ) : ℝ))..(k1:ℝ), f y =
      (∫ y in (((k0 - 1 : ℕ) : ℝ))..a, f y) + ∫ y in a..(k1:ℝ), f y :=
    (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)).symm
  have hfirst : 0 ≤ ∫ y in (((k0 - 1 : ℕ) : ℝ))..a, f y :=
    intervalIntegral.integral_nonneg (by rw [hcast]; linarith) fun y _ => hfnn y
  have hsumint : ∫ y in (((k0 - 1 : ℕ) : ℝ))..(((k1 : ℕ) : ℝ)), f y ≤
      ∑ i ∈ Finset.Ico (k0 - 1) k1, f ((i + 1 : ℕ) : ℝ) := by
    apply MonotoneOn.integral_le_sum_Ico (by omega)
    intro x hx y hy hxy
    exact hfmono (Set.mem_Iic.mpr (by linarith [hx.2])) (Set.mem_Iic.mpr (by linarith [hy.2]))
      hxy
  have hreidx : ∑ i ∈ Finset.Ico (k0 - 1) k1, f ((i + 1 : ℕ) : ℝ) =
      ∑ k ∈ Finset.Icc k0 k1, f k := by
    rw [Finset.sum_Ico_add' (fun i : ℕ => f (i : ℝ)) (k0 - 1) k1 1]
    have : k0 - 1 + 1 = k0 := by omega
    rw [this]; rfl
  rw [hreidx] at hsumint
  have hfsum : G - g (-3) / s ≤ ∑ k ∈ Finset.Icc k0 k1, f k := by linarith
  have hpt : ∀ k ∈ Finset.Icc k0 k1, (1 - 110 / s) * f k ≤ poissonPMFReal t.toNNReal k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hka : a ≤ (k:ℝ) := Nat.ceil_le.mp hk.1
    have hkb : (k:ℝ) ≤ b := (Nat.le_floor_iff hb0).mp hk.2
    exact pmf_lower_below T' k (by linarith) (by linarith) (by linarith)
  have hc0 : 0 ≤ 1 - 110 / s := by
    rw [sub_nonneg, div_le_one hspos]; linarith
  have hmain : (1 - 110 / s) * (G - g (-3) / s) ≤
      ∑ k ∈ Finset.Icc k0 k1, poissonPMFReal t.toNNReal k := by
    calc (1 - 110 / s) * (G - g (-3) / s) ≤ (1 - 110 / s) * ∑ k ∈ Finset.Icc k0 k1, f k :=
          mul_le_mul_of_nonneg_left hfsum hc0
      _ = ∑ k ∈ Finset.Icc k0 k1, (1 - 110 / s) * f k := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum hpt
  have hexp : (1 - 110 / s) * (G - g (-3) / s) =
      G - (110 * G + g (-3)) / s + 110 * g (-3) / (s * s) := by
    field_simp; ring
  have h3 : 0 ≤ 110 * g (-3) / (s * s) := by
    have := gaussianPDFReal_nonneg 0 1 (-3); positivity
  have h4 : (110 * G + g (-3)) / s ≤ 0.9496 / s :=
    div_le_div_of_nonneg_right (by linarith) hspos.le
  linarith
