-- Prove2me | solution 1 for ProbEffIS.GE.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:48:02.014398+00:00
-- url     : https://prove2.me/submissions/64660203-8522-4edf-8c12-f92f1e37d2ae

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory

namespace ProbEffIS.GE

/-- Chebyshev's inequality for the mean of `n` i.i.d. samples. -/
lemma cheb_sampleMean {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (n : ℕ) (hn : 1 ≤ n) (Z : Ω → ℝ) (hZ : MemLp Z 2 Q) (t : ℝ) (ht : 0 < t) :
    Measure.pi (fun _ : Fin n => Q) {ω | t ≤ |sampleMean n Z ω - ∫ x, Z x ∂Q|} ≤
      ENNReal.ofReal (variance Z Q / (n * t ^ 2)) := by
  set P := Measure.pi (fun _ : Fin n => Q)
  have hY : ∀ i : Fin n, MemLp (fun ω : Fin n → Ω => Z (ω i)) 2 P := fun i =>
    hZ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => Q) i)
  have hsumL : MemLp (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i)) 2 P := memLp_finsetSum' _ (fun i _ => hY i)
  have hfun : (fun ω => sampleMean n Z ω) = fun ω => (n : ℝ)⁻¹ * (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i)) ω := by
    funext ω; simp [sampleMean, Finset.sum_apply]
  have hX : MemLp (fun ω => sampleMean n Z ω) 2 P := by
    rw [hfun]; exact hsumL.const_mul _
  have hint : ∀ i : Fin n, ∫ ω, Z (ω i) ∂P = ∫ x, Z x ∂Q := fun i => by
    have hm := (measurePreserving_eval (fun _ : Fin n => Q) i)
    conv_rhs => rw [← hm.map_eq]
    rw [integral_map (measurable_pi_apply i).aemeasurable (by rw [hm.map_eq]; exact hZ.1)]
  have hmean : ∫ ω, sampleMean n Z ω ∂P = ∫ x, Z x ∂Q := by
    simp only [sampleMean]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hY i).integrable one_le_two)]
    simp only [hint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hvar : variance (fun ω => sampleMean n Z ω) P = variance Z Q / n := by
    rw [hfun]
    have h1 : variance (fun ω => (n : ℝ)⁻¹ * (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i)) ω) P
        = ((n : ℝ)⁻¹) ^ 2 * variance (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i)) P := by
      have := variance_const_mul (μ := P) ((n : ℝ)⁻¹) (∑ i : Fin n, fun ω : Fin n → Ω => Z (ω i))
      simpa [Pi.mul_def] using this
    rw [h1, variance_sum_pi (μ := fun _ : Fin n => Q) (X := fun _ => Z) (fun _ => hZ)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hc := meas_ge_le_variance_div_sq hX ht
  rw [hmean, hvar] at hc
  convert hc using 2
  field_simp

lemma minRelDisc_nonneg {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (n : ℕ) (Z : Ω → ℝ)
    (p ε : ℝ) : 0 ≤ minRelDisc Q n Z p ε :=
  Real.sInf_nonneg (fun _ h => h.1.le)

lemma minRelDisc_le {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (n : ℕ) (Z : Ω → ℝ)
    (p ε δ₀ : ℝ) (hδ₀ : 0 ≤ δ₀)
    (h : ∀ δ, δ₀ < δ → Measure.pi (fun _ : Fin n => Q)
      {ω | δ * p < |sampleMean n Z ω - p|} ≤ ENNReal.ofReal ε) :
    minRelDisc Q n Z p ε ≤ δ₀ := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  exact csInf_le ⟨0, fun _ h => h.1.le⟩ ⟨by linarith, h c hc⟩


lemma tendsto_negLog_atTop (p : ℝ → ℝ) (hp : Tendsto p atTop (𝓝 0))
    (hpos : ∀ᶠ γ in atTop, 0 < p γ) : Tendsto (fun γ => -Real.log (p γ)) atTop atTop := by
  have h1 : Tendsto p atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hp, hpos⟩
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)

lemma tendsto_log_div_self : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

end ProbEffIS.GE

open ProbEffIS.GE in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (Q : ℝ → Measure Ω) (hQ : ∀ᶠ γ in atTop, IsProbabilityMeasure (Q γ))
    (Z : ℝ → Ω → ℝ)
    (p : ℝ → ℝ) (hp0 : ∀ γ, 0 ≤ p γ) (hp : Tendsto p atTop (𝓝 0))
    (hunb : ∀ᶠ γ in atTop, ∫ ω, Z γ ω ∂(Q γ) = p γ)
    (hAE : AsymptoticallyEfficient Q Z p) :
    StronglyProbEfficient Q Z p := by
  obtain ⟨hL2, hratio⟩ := hAE
  set m : ℝ → ℝ := fun γ => ∫ ω, Z γ ω ^ 2 ∂(Q γ) with hm_def
  set L : ℝ → ℝ := fun γ => -Real.log (p γ) with hL_def
  have hev_ratio : ∀ᶠ γ in atTop, 1 < Real.log (m γ) / Real.log (p γ) ∧
      Real.log (m γ) / Real.log (p γ) < 3 :=
    (hratio.eventually (Ioo_mem_nhds (by norm_num : (1:ℝ) < 2) (by norm_num : (2:ℝ) < 3))).mono
      fun γ h => h
  have hpos : ∀ᶠ γ in atTop, 0 < p γ := by
    filter_upwards [hev_ratio] with γ h
    rcases (hp0 γ).lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [← h'] at h; simp at h; linarith
  have hLtop : Tendsto L atTop atTop := tendsto_negLog_atTop p hp hpos
  have hL1 : ∀ᶠ γ in atTop, 1 ≤ L γ := hLtop.eventually_ge_atTop 1
  -- `m ≥ p²` eventually
  have hmge : ∀ᶠ γ in atTop, p γ ^ 2 ≤ m γ := by
    filter_upwards [hQ, hL2, hunb] with γ hQγ hL2γ hu
    have := variance_eq_sub hL2γ
    have h0 := variance_nonneg (Z γ) (Q γ)
    rw [this] at h0
    have : (Q γ)[Z γ ^ 2] = m γ := rfl
    rw [hu] at h0
    linarith
  set g : ℝ → ℝ := fun γ => m γ / p γ ^ 2 with hg_def
  have hg1 : ∀ᶠ γ in atTop, 1 ≤ g γ := by
    filter_upwards [hmge, hpos] with γ h hp'
    rw [hg_def]; dsimp only
    rw [le_div_iff₀ (by positivity)]; linarith
  -- log g / L → 0
  have hlogg : Tendsto (fun γ => Real.log (g γ) / L γ) atTop (𝓝 0) := by
    have h2 : Tendsto (fun γ => 2 - Real.log (m γ) / Real.log (p γ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (2:ℝ))).sub hratio
    refine h2.congr' ?_
    filter_upwards [hpos, hmge, hL1] with γ hp' hmg hl
    have hm0 : 0 < m γ := lt_of_lt_of_le (by positivity) hmg
    have hlp : Real.log (p γ) ≠ 0 := by
      intro h; simp only [hL_def, h] at hl; norm_num at hl
    simp only [hg_def, hL_def]
    rw [Real.log_div hm0.ne' (by positivity), Real.log_pow]
    field_simp
    push_cast; ring
  -- the sample sizes
  let n : ℝ → ℕ := fun γ => ⌈g γ * L γ⌉₊ + 1
  have hn1 : ∀ γ, 1 ≤ n γ := fun γ => by simp [n]
  have hnge : ∀ γ, g γ * L γ ≤ (n γ : ℝ) := fun γ => by
    simp only [n]; push_cast; linarith [Nat.le_ceil (g γ * L γ)]
  have hnle : ∀ᶠ γ in atTop, (n γ : ℝ) ≤ 3 * (g γ * L γ) := by
    filter_upwards [hg1, hL1] with γ hg hl
    have h1 : 1 ≤ g γ * L γ := by nlinarith
    simp only [n]; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ g γ * L γ by linarith)
    linarith
  refine ⟨hp, n, hn1, ?_, ?_⟩
  · -- subexponential growth
    show Tendsto (fun γ => Real.log (n γ : ℝ) / L γ) atTop (𝓝 0)
    have hup : Tendsto (fun γ => Real.log 3 / L γ + Real.log (g γ) / L γ +
        Real.log (L γ) / L γ) atTop (𝓝 0) := by
      have a1 : Tendsto (fun γ => Real.log 3 / L γ) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hLtop
      have a3 : Tendsto (fun γ => Real.log (L γ) / L γ) atTop (𝓝 0) :=
        tendsto_log_div_self.comp hLtop
      simpa using (a1.add hlogg).add a3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hL1] with γ hl
      apply div_nonneg _ (by linarith)
      exact Real.log_nonneg (by exact_mod_cast hn1 γ)
    · filter_upwards [hL1, hg1, hnle] with γ hl hg hle
      rw [← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ (by linarith)
      rw [← Real.log_mul (by norm_num) (by linarith), ← Real.log_mul (by positivity) (by linarith)]
      apply Real.log_le_log (by exact_mod_cast hn1 γ)
      linarith
  · intro ε hε
    have hbound : Tendsto (fun γ => Real.sqrt (1 / (ε * L γ))) atTop (𝓝 0) := by
      have : Tendsto (fun γ => 1 / (ε * L γ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (hLtop.const_mul_atTop hε)
      have := (Real.continuous_sqrt.tendsto 0).comp this
      simpa [Function.comp_def] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (Eventually.of_forall fun γ => minRelDisc_nonneg _ _ _ _ _) ?_
    filter_upwards [hQ, hL2, hunb, hpos, hL1, hg1, hmge] with γ hQγ hL2γ hu hp' hl hg hmg
    have hm0 : 0 < m γ := lt_of_lt_of_le (by positivity) hmg
    have hn0 : (0 : ℝ) < n γ := by exact_mod_cast hn1 γ
    set δ₀ := Real.sqrt (g γ / (ε * n γ)) with hδ₀
    have hδ₀le : δ₀ ≤ Real.sqrt (1 / (ε * L γ)) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := hnge γ
      nlinarith
    refine le_trans (minRelDisc_le _ _ _ _ _ δ₀ (Real.sqrt_nonneg _) fun δ hδ => ?_) hδ₀le
    have hδpos : 0 < δ := lt_of_le_of_lt (Real.sqrt_nonneg _) hδ
    have hsub : {ω : Fin (n γ) → Ω | δ * p γ < |sampleMean (n γ) (Z γ) ω - p γ|} ⊆
        {ω | δ * p γ ≤ |sampleMean (n γ) (Z γ) ω - ∫ x, Z γ x ∂(Q γ)|} := by
      intro ω h; simp only [Set.mem_ofPred_eq] at h ⊢; rw [hu]; exact h.le
    refine (measure_mono hsub).trans ((cheb_sampleMean (Q γ) (n γ) (hn1 γ) (Z γ) hL2γ
      (δ * p γ) (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_))
    have hvar : variance (Z γ) (Q γ) ≤ m γ := variance_le_expectation_sq hL2γ.1
    have hδsq : g γ / (ε * n γ) < δ ^ 2 := by
      have h0 : 0 ≤ g γ / (ε * n γ) := by positivity
      have := Real.sqrt_lt' hδpos |>.1 hδ
      exact this
    rw [div_le_iff₀ (by positivity)]
    simp only [hg_def] at hδsq
    rw [div_lt_iff₀ (by positivity)] at hδsq
    have : m γ / p γ ^ 2 * (p γ ^ 2) = m γ := by field_simp
    nlinarith [sq_nonneg (p γ), mul_pos hε hn0]
