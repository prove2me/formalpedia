-- Prove2me | solution 1 for ZipfLaw.zipf_one_leadingDigit_benford
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:59:43.802773+00:00
-- url     : https://prove2.me/submissions/5fa950e9-811f-44ac-adeb-d6a15042a43f

import Definitions.Def_ZipfLaw_Defs

set_option autoImplicit false

open ZipfLaw Filter Topology

private noncomputable def zipf_digitWeight (d N : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ico 1 N).filter (fun k => leadingDigit k = d), 1 / (k : ℝ)

private noncomputable def zipf_digitBlock (d j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico (d * 10 ^ j) ((d + 1) * 10 ^ j), 1 / (k : ℝ)

private lemma zipf_Ico_harmonic (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Ico 1 n, 1 / (k : ℝ)) = genHarmonic (n - 1) 1 := by
  unfold genHarmonic
  simp only [Real.rpow_one]
  rw [← Finset.Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hn]

private lemma zipf_harmonic_real (n : ℕ) : genHarmonic n 1 = (harmonic n : ℝ) := by
  induction n with
  | zero => simp [genHarmonic]
  | succ n ih =>
    unfold genHarmonic
    rw [Finset.sum_Icc_succ_top (by omega), harmonic_succ]
    push_cast
    change genHarmonic n 1 + 1 / ((n : ℝ) + 1) ^ (1 : ℝ) = _
    rw [ih]
    simp [one_div]

private lemma zipf_block_harmonic (d j : ℕ) (hd : 1 ≤ d) :
    zipf_digitBlock d j = genHarmonic ((d + 1) * 10 ^ j - 1) 1 -
      genHarmonic (d * 10 ^ j - 1) 1 := by
  have hp : 1 ≤ 10 ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ha : 1 ≤ d * 10 ^ j := by nlinarith
  have hab : d * 10 ^ j ≤ (d + 1) * 10 ^ j := by nlinarith
  have h := Finset.sum_Ico_consecutive (fun k : ℕ => 1 / (k : ℝ)) ha hab
  rw [zipf_Ico_harmonic _ ha, zipf_Ico_harmonic _ (le_trans ha hab)] at h
  unfold zipf_digitBlock
  linarith

private lemma zipf_power_blocks (d M : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    zipf_digitWeight d (10 ^ M) = ∑ j ∈ Finset.range M, zipf_digitBlock d j := by
  classical
  let T := (Finset.Ico 1 (10 ^ M)).filter (fun k => leadingDigit k = d)
  have hmap : (T : Set ℕ).MapsTo (Nat.log 10) (Finset.range M) := by
    intro k hk
    have hkI := Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1
    apply Finset.mem_range.mpr
    exact (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hkI.2
  have hfiber (j : ℕ) (hj : j ∈ Finset.range M) :
      T.filter (fun k => Nat.log 10 k = j) = Finset.Ico (d * 10 ^ j) ((d + 1) * 10 ^ j) := by
    have hjM : j < M := Finset.mem_range.mp hj
    have hp : 0 < 10 ^ j := by positivity
    ext k
    simp only [T, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hkI, hlead⟩, hlog⟩
      have hdiv : k / 10 ^ j = d := by simpa only [leadingDigit, hlog] using hlead
      constructor
      · simpa only [hdiv] using Nat.div_mul_le_self k (10 ^ j)
      · apply (Nat.div_lt_iff_lt_mul hp).mp
        omega
    · intro hk
      have hkp : 10 ^ j ≤ k := by nlinarith [Nat.one_le_iff_ne_zero.mpr hp.ne']
      have hk10 : k < 10 ^ (j + 1) := by
        rw [pow_succ]
        nlinarith
      have hlog : Nat.log 10 k = j := Nat.log_eq_of_pow_le_of_lt_pow hkp hk10
      have hk1 : 1 ≤ k := le_trans (by omega) hkp
      have hkM : k < 10 ^ M := lt_of_lt_of_le hk10
        (pow_le_pow_right₀ (by norm_num : 1 ≤ (10 : ℕ)) (by omega))
      have hdivlo : d ≤ k / 10 ^ j := (Nat.le_div_iff_mul_le hp).mpr hk.1
      have hdivhi : k / 10 ^ j < d + 1 := (Nat.div_lt_iff_lt_mul hp).mpr hk.2
      refine ⟨⟨⟨hk1, hkM⟩, ?_⟩, hlog⟩
      unfold leadingDigit
      rw [hlog]
      omega
  unfold zipf_digitWeight
  change (∑ k ∈ T, 1 / (k : ℝ)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun k : ℕ => 1 / (k : ℝ))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hfiber j hj]
  rfl

private lemma zipf_cutoff_atTop (a : ℕ) (ha : 1 ≤ a) :
    Tendsto (fun j : ℕ => a * 10 ^ j - 1) atTop atTop := by
  have hpr : Tendsto (fun j : ℕ => (10 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hp : Tendsto (fun j : ℕ => (10 : ℕ) ^ j) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpr)
  have hmul : Tendsto (fun j : ℕ => a * 10 ^ j) atTop atTop := by
    apply tendsto_atTop_mono _ hp
    intro j
    simpa only [one_mul] using Nat.mul_le_mul_right (10 ^ j) ha
  exact (tendsto_sub_atTop_nat 1).comp hmul

private lemma zipf_log_cutoff (a j : ℕ) (ha : 1 ≤ a) :
    Real.log (((a * 10 ^ j - 1 : ℕ) : ℝ) + 1) =
      Real.log (a : ℝ) + (j : ℝ) * Real.log 10 := by
  have hp : 1 ≤ 10 ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hap : 1 ≤ a * 10 ^ j := by nlinarith
  have heq : (((a * 10 ^ j - 1 : ℕ) : ℝ) + 1) = (a : ℝ) * (10 : ℝ) ^ j := by
    calc
      _ = (((a * 10 ^ j - 1) + 1 : ℕ) : ℝ) := by push_cast; rfl
      _ = ((a * 10 ^ j : ℕ) : ℝ) := by rw [Nat.sub_add_cancel hap]
      _ = _ := by push_cast; rfl
  rw [heq]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]

private lemma zipf_block_limit (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (zipf_digitBlock d) atTop
      (nhds (Real.log ((d : ℝ) + 1) - Real.log (d : ℝ))) := by
  have ha := Real.tendsto_harmonic_sub_log_add_one.comp (zipf_cutoff_atTop d hd)
  have hb := Real.tendsto_harmonic_sub_log_add_one.comp (zipf_cutoff_atTop (d + 1) (by omega))
  have h := (hb.sub ha).add_const (Real.log ((d : ℝ) + 1) - Real.log (d : ℝ))
  simp only [sub_self, zero_add] at h
  apply h.congr
  intro j
  dsimp only [Function.comp_apply]
  rw [← zipf_harmonic_real, ← zipf_harmonic_real, zipf_log_cutoff _ _ (by omega),
    zipf_log_cutoff _ _ hd, zipf_block_harmonic _ _ hd]
  push_cast
  ring

private lemma zipf_weight_limit (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Tendsto (fun M : ℕ => zipf_digitWeight d (10 ^ M) / (M : ℝ)) atTop
      (nhds (Real.log ((d : ℝ) + 1) - Real.log (d : ℝ))) := by
  simpa only [zipf_power_blocks d _ hd1 hd9, div_eq_mul_inv, mul_comm] using
    (zipf_block_limit d hd1).cesaro

private lemma zipf_normalizer_limit :
    Tendsto (fun M : ℕ => genHarmonic (10 ^ M - 1) 1 / (M : ℝ)) atTop
      (nhds (Real.log 10)) := by
  have he := Real.tendsto_harmonic_sub_log_add_one.comp (zipf_cutoff_atTop 1 (by norm_num))
  have herr : Tendsto (fun M : ℕ => genHarmonic (10 ^ M - 1) 1 - (M : ℝ) * Real.log 10)
      atTop (nhds Real.eulerMascheroniConstant) := by
    apply he.congr
    intro M
    dsimp only [Function.comp_apply]
    rw [one_mul, ← zipf_harmonic_real]
    simpa only [one_mul, Nat.cast_one, Real.log_one, zero_add] using
      congrArg (fun x => genHarmonic (10 ^ M - 1) 1 - x) (zipf_log_cutoff 1 M (by norm_num))
  have h := (herr.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))).add_const (Real.log 10)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp
  <;> ring

private lemma zipf_shift_quotient {f : ℕ → ℝ} {c : ℝ}
    (hf : Tendsto (fun M : ℕ => f M / (M : ℝ)) atTop (nhds c)) :
    Tendsto (fun M : ℕ => f (M + 1) / (M : ℝ)) atTop (nhds c) := by
  have hr : Tendsto (fun M : ℕ => ((M : ℝ) + 1) / (M : ℝ)) atTop (nhds (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have h' := h.const_add 1
    simp only [add_zero] at h'
    apply h'.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    field_simp
  have h := (hf.comp (tendsto_add_atTop_nat 1)).mul hr
  simp only [mul_one] at h
  apply h.congr
  intro M
  dsimp only [Function.comp_apply]
  rw [Nat.cast_add, Nat.cast_one, ← mul_div_assoc,
    div_mul_cancel₀ _ (show (M : ℝ) + 1 ≠ 0 by positivity)]

private lemma zipf_weight_mono (d : ℕ) : Monotone (zipf_digitWeight d) := by
  intro N M hNM
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    have h := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨(Finset.mem_Ico.mp h.1).1, lt_of_lt_of_le (Finset.mem_Ico.mp h.1).2 hNM⟩, h.2⟩
  · intro k _ _
    positivity

private lemma zipf_harmonic_mono : Monotone (fun N : ℕ => genHarmonic N 1) := by
  intro N M hNM
  unfold genHarmonic
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    have h := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨h.1, le_trans h.2 hNM⟩
  · intro k _ _
    positivity

private lemma zipf_harmonic_positive (N : ℕ) (hN : 1 ≤ N) : 0 < genHarmonic N 1 := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity) ⟨1, by simp [hN], by norm_num⟩

private lemma zipf_nat_log_atTop : Tendsto (fun N : ℕ => Nat.log 10 (N + 1)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (10 ^ b)] with N hN
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

private lemma zipf_digit_probability (d N : ℕ) :
    (∑ k ∈ (Finset.Icc 1 N).filter (fun k => leadingDigit k = d), zipfPMF N 1 k) =
      zipf_digitWeight d (N + 1) / genHarmonic N 1 := by
  unfold zipf_digitWeight
  rw [Finset.Ico_add_one_right_eq_Icc, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zipfPMF, if_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1), Real.rpow_one]

theorem solution (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ (Finset.Icc 1 N).filter (fun k => leadingDigit k = d), zipfPMF N 1 k)
      Filter.atTop (nhds (Real.logb 10 (1 + 1 / (d : ℝ)))) := by
  let c := Real.log ((d : ℝ) + 1) - Real.log (d : ℝ)
  let A := fun M : ℕ => zipf_digitWeight d (10 ^ M)
  let H := fun M : ℕ => genHarmonic (10 ^ M - 1) 1
  have hA : Tendsto (fun M : ℕ => A M / (M : ℝ)) atTop (nhds c) :=
    zipf_weight_limit d hd1 hd9
  have hH : Tendsto (fun M : ℕ => H M / (M : ℝ)) atTop (nhds (Real.log 10)) :=
    zipf_normalizer_limit
  have hlog : Real.log (10 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlower : Tendsto (fun M : ℕ => A M / H (M + 1)) atTop (nhds (c / Real.log 10)) := by
    have h := hA.div (zipf_shift_quotient hH) hlog
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    exact div_div_div_cancel_right₀ (by exact_mod_cast (show M ≠ 0 by omega)) _ _
  have hupper : Tendsto (fun M : ℕ => A (M + 1) / H M) atTop (nhds (c / Real.log 10)) := by
    have h := (zipf_shift_quotient hA).div hH hlog
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    exact div_div_div_cancel_right₀ (by exact_mod_cast (show M ≠ 0 by omega)) _ _
  have hprob : Tendsto (fun N : ℕ => zipf_digitWeight d (N + 1) / genHarmonic N 1)
      atTop (nhds (c / Real.log 10)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hlower.comp zipf_nat_log_atTop) (hupper.comp zipf_nat_log_atTop)
    · filter_upwards [zipf_nat_log_atTop.eventually (eventually_ge_atTop 1)] with N hM
      let M := Nat.log 10 (N + 1)
      have hlo : 10 ^ M ≤ N + 1 := Nat.pow_log_le_self 10 (by omega)
      have hhi : N + 1 < 10 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have hP : 1 < 10 ^ M := lt_of_lt_of_le (by norm_num : 1 < (10 : ℕ) ^ 1)
        (pow_le_pow_right₀ (by norm_num : 1 ≤ (10 : ℕ)) hM)
      have hN : 1 ≤ N := by omega
      have hn := zipf_harmonic_positive N hN
      have hH1 : 0 < H (M + 1) := zipf_harmonic_positive _ (by
        have := pow_le_pow_right₀ (by norm_num : 1 ≤ (10 : ℕ)) (Nat.le_succ M)
        omega)
      have hnon : 0 ≤ zipf_digitWeight d (N + 1) := Finset.sum_nonneg (fun _ _ => by positivity)
      change A M / H (M + 1) ≤ _
      calc
        _ ≤ zipf_digitWeight d (N + 1) / H (M + 1) :=
          div_le_div_of_nonneg_right (zipf_weight_mono d hlo) hH1.le
        _ ≤ _ := div_le_div_of_nonneg_left hnon hn (zipf_harmonic_mono (by omega))
    · filter_upwards [zipf_nat_log_atTop.eventually (eventually_ge_atTop 1)] with N hM
      let M := Nat.log 10 (N + 1)
      have hlo : 10 ^ M ≤ N + 1 := Nat.pow_log_le_self 10 (by omega)
      have hhi : N + 1 < 10 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have hP : 1 < 10 ^ M := lt_of_lt_of_le (by norm_num : 1 < (10 : ℕ) ^ 1)
        (pow_le_pow_right₀ (by norm_num : 1 ≤ (10 : ℕ)) hM)
      have hN : 1 ≤ N := by omega
      have hn := zipf_harmonic_positive N hN
      have hH0 : 0 < H M := zipf_harmonic_positive _ (by omega)
      have hnon : 0 ≤ A (M + 1) := Finset.sum_nonneg (fun _ _ => by positivity)
      change _ ≤ A (M + 1) / H M
      calc
        _ ≤ A (M + 1) / genHarmonic N 1 :=
          div_le_div_of_nonneg_right (zipf_weight_mono d hhi.le) hn.le
        _ ≤ _ := div_le_div_of_nonneg_left hnon hH0 (zipf_harmonic_mono (by omega))
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hvalue : c / Real.log 10 = Real.logb 10 (1 + 1 / (d : ℝ)) := by
    rw [Real.logb, show 1 + 1 / (d : ℝ) = ((d : ℝ) + 1) / d by field_simp,
      Real.log_div (by positivity) hdpos.ne']
  rw [hvalue] at hprob
  simpa only [zipf_digit_probability] using hprob

#print axioms solution
