-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.qubitLeadingAsymptotic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:31:47.68969+00:00
-- url     : https://prove2.me/submissions/527bd7bb-404b-4fc5-822d-011864a20359

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

open QAlgorithms.Papers.Independent.Gap48.P40

lemma g78a_logR (u : ℝ) (hu : |u| ≤ 1/2) :
    |(1 + u) * Real.log (1 + u) - u - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have h1 : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at h
  norm_num at h
  have hden : 1 / 2 ≤ 1 - |u| := by linarith
  have hE : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 2 * |u| ^ 3 := by
    have : |u| ^ 3 / (1 - |u|) ≤ 2 * |u| ^ 3 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg (abs_nonneg u) 3]
    have e : Real.log (1 + u) - u + u ^ 2 / 2 = -u + u ^ 2 / 2 + Real.log (1 + u) := by ring
    rw [e]; exact h.trans this
  set E := Real.log (1 + u) - u + u ^ 2 / 2 with hEdef
  have key : (1 + u) * Real.log (1 + u) - u - u ^ 2 / 2 = -u ^ 3 / 2 + (1 + u) * E := by
    rw [hEdef]; ring
  rw [key]
  have hu3 : |u ^ 3| = |u| ^ 3 := abs_pow u 3
  calc |-u ^ 3 / 2 + (1 + u) * E| ≤ |-u ^ 3 / 2| + |(1 + u) * E| := abs_add_le _ _
    _ = |u| ^ 3 / 2 + |1 + u| * |E| := by rw [abs_mul, abs_div, abs_neg, hu3]; norm_num
    _ ≤ |u| ^ 3 / 2 + (3 / 2) * (2 * |u| ^ 3) := by
        gcongr
        · rw [abs_le] at hu ⊢; constructor <;> linarith
    _ ≤ 4 * |u| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg u) 3]

lemma g78a_lim {f : ℝ → ℝ} {L C δ : ℝ} (hδ : 0 < δ)
    (h : ∀ T, 0 < T → T < δ → |f T - L * T ^ 2| ≤ C * T ^ 3) :
    Tendsto (fun T => f T / T ^ 2) (𝓝[>] 0) (𝓝 L) := by
  have hg : Tendsto (fun T => f T / T ^ 2 - L) (𝓝[>] 0) (𝓝 0) := by
    have hC : Tendsto (fun T : ℝ => C * T) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun T : ℝ => C * T) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    apply squeeze_zero_norm' _ hC
    have : ∀ᶠ T in 𝓝[>] (0:ℝ), T ∈ Set.Ioo 0 δ := Ioo_mem_nhdsGT hδ
    filter_upwards [this] with T hT
    obtain ⟨h0, h1⟩ := hT
    have hT2 : 0 < T ^ 2 := by positivity
    have e : f T / T ^ 2 - L = (f T - L * T ^ 2) / T ^ 2 := by field_simp
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos hT2, div_le_iff₀ hT2]
    calc |f T - L * T ^ 2| ≤ C * T ^ 3 := h T h0 h1
      _ = C * T * T ^ 2 := by ring
  have := hg.add_const L
  simpa using this

lemma g78a_series (u : ℝ) (hu : |u| < 1) :
    HasSum (fun k : ℕ => u ^ (2 * (k + 1)) / (((k + 1 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) - 1)))
      ((1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u)) := by
  have hu2 : |u ^ 2| < 1 := by
    rw [abs_pow]; have := abs_nonneg u; nlinarith
  have A := Real.hasSum_pow_div_log_of_abs_lt_one hu2
  have B := (Real.hasSum_log_sub_log_of_abs_lt_one hu).mul_left u
  have C := B.sub A
  have hp : 0 < 1 + u := by rw [abs_lt] at hu; linarith
  have hm : 0 < 1 - u := by rw [abs_lt] at hu; linarith
  have hlog : Real.log (1 - u ^ 2) = Real.log (1 + u) + Real.log (1 - u) := by
    rw [← Real.log_mul hp.ne' hm.ne']; ring_nf
  have e2 : (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) =
      u * (Real.log (1 + u) - Real.log (1 - u)) - -Real.log (1 - u ^ 2) := by rw [hlog]; ring
  rw [e2]
  have e1 : (fun k : ℕ => u ^ (2 * (k + 1)) / (((k + 1 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) - 1))) =
      fun b : ℕ => u * (2 * (1 / (2 * (b:ℝ) + 1)) * u ^ (2 * b + 1)) - (u ^ 2) ^ (b + 1) / ((b:ℝ) + 1) := by
    funext k
    push_cast
    have h1 : (0:ℝ) < k + 1 := by positivity
    have h2 : (0:ℝ) < 2 * k + 1 := by positivity
    rw [← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ,
      show (2 * ((k:ℝ) + 1) - 1) = 2 * k + 1 by ring]
    field_simp
    ring
  rw [e1]; exact C

/-- PDF p.10, Eq.(48), correct leading term only. The printed infinite series
is separately deferred; this asymptotic is of the bound (46), not of every entropy. -/
theorem solution (beta : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2) :
    Tendsto (fun T : ℝ => qubitSmallBound beta T / T ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / (2 * beta * (1 - beta)))) := by
  obtain ⟨hb0, hb1⟩ := hbeta
  set a := 1 - beta with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hba : beta ≤ a := by rw [ha]; linarith
  apply g78a_lim (C := 4 / a ^ 2 + 4 / beta ^ 2) (δ := beta / 2) (by linarith)
  intro T hT0 hT1
  set u := T / a with hu
  set v := T / beta with hv
  have hu0 : 0 < u := div_pos hT0 ha0
  have hv0 : 0 < v := div_pos hT0 hb0
  have hv1 : |(-v)| ≤ 1 / 2 := by
    rw [abs_neg, abs_of_pos hv0, hv, div_le_iff₀ hb0]; linarith
  have hu1 : |u| ≤ 1 / 2 := by
    rw [abs_of_pos hu0, hu, div_le_iff₀ ha0]; linarith
  have A := g78a_logR u hu1
  have B := g78a_logR (-v) hv1
  have e : qubitSmallBound beta T - 1 / (2 * beta * (1 - beta)) * T ^ 2 =
      a * ((1 + u) * Real.log (1 + u) - u - u ^ 2 / 2) +
      beta * ((1 + -v) * Real.log (1 + -v) - -v - (-v) ^ 2 / 2) := by
    unfold qubitSmallBound
    have hne : (1 - beta) ≠ 0 := by linarith
    have h1 : (T + 1 - beta) / (1 - beta) = 1 + u := by rw [hu, ha]; field_simp; ring
    have h2 : 1 - T / beta = 1 + -v := by rw [hv]; ring
    rw [h1, h2]
    have h3 : T = a * u := by rw [hu]; field_simp
    have h4 : T = beta * v := by rw [hv]; field_simp
    have h5 : T + 1 - beta = a * (1 + u) := by linear_combination h3 - ha
    rw [h5, ← ha]
    have h6 : beta - T = beta * (1 + -v) := by rw [h4]; ring
    rw [h6]
    have h7 : 1 / (2 * beta * a) * T ^ 2 = a * (u ^ 2 / 2) + beta * (v ^ 2 / 2) := by
      have : a + beta = 1 := by rw [ha]; ring
      field_simp
      rw [h3] at h4 ⊢
      have hv' : v = a * u / beta := by rw [h4]; field_simp
      rw [hv']; field_simp; linear_combination (-(u ^ 2 * a ^ 2 * beta * a)) * this
    rw [h7]; linear_combination h4 - h3
  rw [e]
  have hb : |beta| = beta := abs_of_pos hb0
  have haa : |a| = a := abs_of_pos ha0
  calc _ ≤ |a * ((1 + u) * Real.log (1 + u) - u - u ^ 2 / 2)| +
        |beta * ((1 + -v) * Real.log (1 + -v) - -v - (-v) ^ 2 / 2)| := abs_add_le _ _
    _ ≤ a * (4 * |u| ^ 3) + beta * (4 * |(-v)| ^ 3) := by
        rw [abs_mul, abs_mul, hb, haa]; gcongr
    _ = (4 / a ^ 2 + 4 / beta ^ 2) * T ^ 3 := by
        rw [abs_neg, abs_of_pos hv0, abs_of_pos hu0, hu, hv]; field_simp



end
