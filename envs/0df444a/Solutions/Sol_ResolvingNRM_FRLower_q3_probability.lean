-- Prove2me | solution 1 for ResolvingNRM.FRLower.q3_probability
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:33:14.838037+00:00
-- url     : https://prove2.me/submissions/aac56681-4695-4fda-80de-c7150aa4a380

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

lemma log_le_sinh_form {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ (y - y⁻¹) / 2 := by
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hy)
  rwa [Real.sinh_log (by linarith)] at h

lemma pmf_lower (T : ℕ) (hT : 1 ≤ T) (k : ℕ) (hk1 : (T:ℝ) ≤ k)
    (hk2 : (k:ℝ) - T ≤ 7 * √(T:ℝ)) :
    (1 - 4 / √(T:ℝ)) * (ProbabilityTheory.gaussianPDFReal 0 1 (((k:ℝ) - T) / √(T:ℝ)) / √(T:ℝ))
      ≤ ProbabilityTheory.poissonPMFReal (T:ℝ).toNNReal k := by
  set t : ℝ := (T:ℝ) with ht
  set s : ℝ := √t with hs
  set kk : ℝ := (k:ℝ) with hkk
  have ht1 : (1:ℝ) ≤ t := by rw [ht]; exact_mod_cast hT
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1
  have hss : s * s = t := Real.mul_self_sqrt (by linarith)
  have hk0 : 1 ≤ kk := le_trans ht1 hk1
  have hkpos : 0 < kk := by linarith
  have hk1n : 1 ≤ k := by rw [hkk] at hk0; exact_mod_cast hk0
  have hfac := stirling_upper k hk1n
  rw [← hkk] at hfac
  unfold ProbabilityTheory.poissonPMFReal
  rw [Real.coe_toNNReal _ (by linarith)]
  -- lower bound by replacing factorial
  have hD : 0 < √(2 * π * kk) * (kk / exp 1) ^ k * exp (1 / (12 * kk)) := by positivity
  have step1 : exp (-t) * t ^ k / (√(2 * π * kk) * (kk / exp 1) ^ k * exp (1 / (12 * kk)))
      ≤ exp (-t) * t ^ k / (k ! : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
  refine le_trans ?_ step1
  -- rewrite as exponential
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
  -- left side
  unfold ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hx2 : ((kk - t) / s) ^ 2 = (kk - t) ^ 2 / t := by
    rw [div_pow, ← hss]; ring
  rw [hx2]
  have hc : 0 < √(2 * π) * s := by positivity
  have hL : (1 - 4 / s) * ((√(2 * π))⁻¹ * exp (-((kk - t) ^ 2 / t) / 2) / s)
      ≤ exp (-4 / s) * exp (-((kk - t) ^ 2 / t) / 2) / (√(2 * π) * s) := by
    have h1 : 1 - 4 / s ≤ exp (-4 / s) := by
      have := Real.add_one_le_exp (-4 / s); linarith [show -4 / s = -(4/s) by ring]
    rw [show (1 - 4 / s) * ((√(2 * π))⁻¹ * exp (-((kk - t) ^ 2 / t) / 2) / s)
        = (1 - 4 / s) * exp (-((kk - t) ^ 2 / t) / 2) / (√(2 * π) * s) by field_simp]
    gcongr
  refine le_trans hL ?_
  rw [← Real.exp_add]
  gcongr
  -- exponent inequality
  have hlog : Real.log (kk / t) = Real.log kk - Real.log t :=
    Real.log_div (by linarith) (by linarith)
  have hy : 1 ≤ kk / t := by rw [le_div_iff₀ (by linarith)]; linarith
  have hA := log_le_sinh_form hy
  have hB := Real.log_le_sub_one_of_pos (show 0 < kk / t by positivity)
  rw [hlog] at hA hB
  have hA' : kk * (Real.log kk - Real.log t) ≤ (kk ^ 2 - t ^ 2) / (2 * t) := by
    have : kk * ((kk / t - (kk / t)⁻¹) / 2) = (kk ^ 2 - t ^ 2) / (2 * t) := by
      field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hA (by linarith)
  have hC : (kk - t) / (2 * t) ≤ 7 / (2 * s) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith), ← hss]
    nlinarith
  have hD' : 1 / (12 * kk) ≤ 1 / (12 * s) := by
    apply one_div_le_one_div_of_le (by linarith)
    nlinarith
  have hE : (kk / t - 1) = (kk - t) / t := by field_simp
  have key : -4 / s ≤ -((kk - t) / (2 * t)) - 1 / (12 * kk) := by
    have e : 7 / (2 * s) + 1 / (12 * s) = (43 / 12) / s := by field_simp; ring
    have : (43 / 12) / s ≤ 4 / s := div_le_div_of_nonneg_right (by norm_num) (by linarith)
    have e2 : -4 / s = -(4 / s) := by ring
    linarith
  have hsq : -((kk - t) ^ 2 / t) / 2 = -t + kk - (kk ^ 2 - t ^ 2) / (2 * t) := by
    field_simp; ring
  rw [hsq, hlog]
  have hB' : (Real.log kk - Real.log t) / 2 ≤ (kk - t) / (2 * t) := by
    have : (kk / t - 1) / 2 = (kk - t) / (2 * t) := by rw [hE]; field_simp
    linarith
  linarith [hA', hB', key]

open MeasureTheory ProbabilityTheory

lemma gauss_cdf_diff :
    cdf (gaussianReal 0 1) 7 - cdf (gaussianReal 0 1) 6 =
      ∫ x in (6:ℝ)..7, gaussianPDFReal 0 1 x := by
  rw [cdf_eq_real, cdf_eq_real, ← measureReal_diff (Set.Iic_subset_Iic.mpr (by norm_num))
    measurableSet_Iic, show Set.Iic (7:ℝ) \ Set.Iic 6 = Set.Ioc 6 7 by
      ext x; simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Ioc, not_le]; tauto,
    intervalIntegral.integral_of_le (by norm_num),
    measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ioc fun x _ => gaussianPDFReal_nonneg 0 1 x

lemma gauss_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gaussianPDFReal 0 1 y ≤ gaussianPDFReal 0 1 x := by
  unfold gaussianPDFReal
  gcongr

lemma gauss_six_le : gaussianPDFReal 0 1 6 ≤ 1 / 19 := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have h1 : (√(2 * π))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  have h2 : rexp (-(6:ℝ) ^ 2 / 2) ≤ 1 / 19 := by
    have e : -(6:ℝ) ^ 2 / 2 = -18 := by norm_num
    rw [e, Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have := Real.add_one_le_exp (18:ℝ); linarith
  calc (√(2 * π))⁻¹ * rexp (-(6:ℝ) ^ 2 / 2) ≤ 1 * (1 / 19) := by
        gcongr
    _ = 1 / 19 := by ring

theorem solution (T' : ℕ) (hT : 1 ≤ T') :
    (∑' k : ℕ, if (T' : ℝ) + 6 * Real.sqrt (T' : ℝ) ≤ (k : ℝ) ∧
        (k : ℝ) ≤ (T' : ℝ) + 7 * Real.sqrt (T' : ℝ) then
        ProbabilityTheory.poissonPMFReal (T' : ℝ).toNNReal k else (0 : ℝ)) ≥
      cdf (gaussianReal 0 1) 7 - cdf (gaussianReal 0 1) 6 -
        0.9496 / Real.sqrt (T' : ℝ) := by
  rw [gauss_cdf_diff]
  set t : ℝ := (T':ℝ) with ht
  set s : ℝ := √t with hs
  set g : ℝ → ℝ := gaussianPDFReal 0 1 with hg
  set G : ℝ := ∫ x in (6:ℝ)..7, g x with hG
  have ht1 : (1:ℝ) ≤ t := by rw [ht]; exact_mod_cast hT
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr ht1
  have hss : s * s = t := Real.mul_self_sqrt (by linarith)
  have hgc : Continuous g := by
    rw [hg]; unfold gaussianPDFReal; fun_prop
  have hg6 := gauss_six_le
  have hG_le : G ≤ g 6 := by
    have : G ≤ ∫ x in (6:ℝ)..7, g 6 := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hgc.intervalIntegrable _ _)
        intervalIntegrable_const
      intro x hx; exact gauss_anti (by norm_num) hx.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hLnn : 0 ≤ ∑' k : ℕ, (if t + 6 * s ≤ (k : ℝ) ∧ (k : ℝ) ≤ t + 7 * s then
        poissonPMFReal t.toNNReal k else (0 : ℝ)) :=
    tsum_nonneg fun k => by split_ifs <;> simp [poissonPMFReal_nonneg]
  rcases lt_or_ge s 4 with hs4 | hs4
  · have : 0.9496 / s ≥ 0.9496 / 4 := div_le_div_of_nonneg_left (by norm_num) (by linarith)
      hs4.le
    show _ ≥ G - 0.9496 / s
    linarith
  -- main case
  set a : ℝ := t + 6 * s with ha
  set b : ℝ := t + 7 * s with hb
  set k0 : ℕ := ⌈a⌉₊ with hk0
  set k1 : ℕ := ⌊b⌋₊ with hk1
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
  -- the tsum is a finite sum
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
  show _ ≥ G - 0.9496 / s
  rw [hsum]
  -- the scaled density
  set f : ℝ → ℝ := fun y => g ((y - t) / s) / s with hf
  have hspos : 0 < s := by linarith
  have hfc : Continuous f := by
    rw [hf]; exact (hgc.comp (by fun_prop)).div_const _
  have hfnn : ∀ y, 0 ≤ f y := fun y => div_nonneg (gaussianPDFReal_nonneg 0 1 _) hspos.le
  have hfanti : AntitoneOn f (Set.Ici t) := by
    intro x hx y hy hxy
    simp only [hf]
    apply div_le_div_of_nonneg_right _ hspos.le
    apply gauss_anti
    · exact div_nonneg (by linarith [Set.mem_Ici.mp hx]) hspos.le
    · exact div_le_div_of_nonneg_right (by linarith) hspos.le
  -- change of variables
  have hcov : ∫ y in a..b, f y = G := by
    have e : ∀ y, f y = s⁻¹ * g (y / s - t / s) := by
      intro y; simp only [hf]; rw [sub_div]; field_simp
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div_sub _
      hspos.ne']
    have e1 : a / s - t / s = 6 := by rw [ha, ← hss]; field_simp; ring
    have e2 : b / s - t / s = 7 := by rw [hb, ← hss]; field_simp; ring
    rw [e1, e2, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hspos.ne', one_mul]
  -- split integral
  have hsplit : ∫ y in a..b, f y = (∫ y in a..(k0:ℝ), f y) + ∫ y in (k0:ℝ)..b, f y :=
    (intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)).symm
  have hfirst : ∫ y in a..(k0:ℝ), f y ≤ g 6 / s := by
    have : ∫ y in a..(k0:ℝ), f y ≤ ∫ y in a..(k0:ℝ), f a := by
      apply intervalIntegral.integral_mono_on hk0a (hfc.intervalIntegrable _ _)
        intervalIntegrable_const
      intro x hx
      exact hfanti (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith [hx.1])) hx.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hfa : f a = g 6 / s := by
      simp only [hf]; congr 2; rw [ha]; field_simp; ring
    rw [hfa] at this
    have h6 : 0 ≤ g 6 / s := div_nonneg (gaussianPDFReal_nonneg 0 1 _) hspos.le
    nlinarith
  have hsecond : ∫ y in (k0:ℝ)..b, f y ≤ ∫ y in (k0:ℝ)..((k1 + 1 : ℕ) : ℝ), f y := by
    have hkb : (k0:ℝ) ≤ b := by exact_mod_cast (le_trans (by exact_mod_cast hk01) hk1b)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (a := (k0:ℝ)) (b := b)
      (c := ((k1 + 1 : ℕ) : ℝ)) (μ := volume) (hfc.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _)
    have : 0 ≤ ∫ y in b..((k1 + 1 : ℕ) : ℝ), f y :=
      intervalIntegral.integral_nonneg (by push_cast; linarith) fun y _ => hfnn y
    linarith
  have hsumint : ∫ y in (k0:ℝ)..((k1 + 1 : ℕ) : ℝ), f y ≤
      ∑ k ∈ Finset.Ico k0 (k1 + 1), f k := by
    apply AntitoneOn.integral_le_sum_Ico (by omega)
    intro x hx y hy hxy
    exact hfanti (Set.mem_Ici.mpr (by linarith [hx.1])) (Set.mem_Ici.mpr (by linarith [hy.1]))
      hxy
  have hIco : Finset.Ico k0 (k1 + 1) = Finset.Icc k0 k1 := rfl
  rw [hIco] at hsumint
  have hfsum : G - g 6 / s ≤ ∑ k ∈ Finset.Icc k0 k1, f k := by linarith
  -- pointwise pmf bound
  have hpt : ∀ k ∈ Finset.Icc k0 k1, (1 - 4 / s) * f k ≤ poissonPMFReal t.toNNReal k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hka : a ≤ (k:ℝ) := Nat.ceil_le.mp hk.1
    have hkb : (k:ℝ) ≤ b := (Nat.le_floor_iff hb0).mp hk.2
    exact pmf_lower T' hT k (by linarith) (by linarith)
  have hc0 : 0 ≤ 1 - 4 / s := by
    rw [sub_nonneg, div_le_one hspos]; exact hs4
  have hmain : (1 - 4 / s) * (G - g 6 / s) ≤ ∑ k ∈ Finset.Icc k0 k1, poissonPMFReal t.toNNReal k := by
    calc (1 - 4 / s) * (G - g 6 / s) ≤ (1 - 4 / s) * ∑ k ∈ Finset.Icc k0 k1, f k :=
          mul_le_mul_of_nonneg_left hfsum hc0
      _ = ∑ k ∈ Finset.Icc k0 k1, (1 - 4 / s) * f k := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum hpt
  have hG0 : 0 ≤ G := intervalIntegral.integral_nonneg (by norm_num)
    fun y _ => gaussianPDFReal_nonneg 0 1 y
  have hexp : (1 - 4 / s) * (G - g 6 / s) = G - (4 * G + g 6) / s + 4 * g 6 / (s * s) := by
    field_simp; ring
  have h3 : 0 ≤ 4 * g 6 / (s * s) := by
    have := gaussianPDFReal_nonneg 0 1 6; positivity
  have h4 : (4 * G + g 6) / s ≤ 0.9496 / s :=
    div_le_div_of_nonneg_right (by linarith) hspos.le
  linarith

