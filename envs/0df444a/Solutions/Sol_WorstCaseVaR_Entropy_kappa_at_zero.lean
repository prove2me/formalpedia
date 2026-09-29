-- Prove2me | solution 1 for WorstCaseVaR.Entropy.kappa_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:18:48.952296+00:00
-- url     : https://prove2.me/submissions/a6d140dd-5861-46a0-908d-298a1b865811

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

open MeasureTheory ProbabilityTheory Filter Topology

/-- The standard normal CDF is continuous. -/
lemma aux_kz_cont : Continuous stdNormalCDF := by
  have hmono : Monotone (cdf (gaussianReal 0 1)) := monotone_cdf _
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hleft : ∀ b : ℝ, Function.leftLim (cdf (gaussianReal 0 1)) b = cdf (gaussianReal 0 1) b := by
    intro b
    have h1 := (cdf (gaussianReal 0 1)).measure_singleton b
    rw [measure_cdf, measure_singleton] at h1
    have h2 : cdf (gaussianReal 0 1) b - Function.leftLim (cdf (gaussianReal 0 1)) b ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp h1.symm
    have h3 := hmono.leftLim_le (le_refl b)
    linarith
  have : Continuous (cdf (gaussianReal 0 1)) := by
    rw [continuous_iff_continuousAt]
    intro b
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, (cdf (gaussianReal 0 1)).right_continuous b⟩
    rw [← continuousWithinAt_Iio_iff_Iic]
    exact (hmono.continuousWithinAt_Iio_iff_leftLim_eq).2 (hleft b)
  exact this

/-- Strict monotonicity of the quantile on `(0,1)`. -/
lemma aux_kz_quant {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    normalQuantile p < normalQuantile q := by
  have hc := aux_kz_cont
  set Sp := {t : ℝ | p ≤ stdNormalCDF t} with hSp
  set Sq := {t : ℝ | q ≤ stdNormalCDF t} with hSq
  -- nonempty
  have hne : Sq.Nonempty := by
    have ht : Tendsto stdNormalCDF atTop (𝓝 1) := tendsto_cdf_atTop _
    have := (ht.eventually (lt_mem_nhds hq)).exists
    obtain ⟨t, ht⟩ := this
    exact ⟨t, le_of_lt ht⟩
  -- bdd below
  have hbddp : BddBelow Sp := by
    have ht : Tendsto stdNormalCDF atBot (𝓝 0) := tendsto_cdf_atBot _
    obtain ⟨T, hT⟩ := eventually_atBot.1 (ht.eventually (gt_mem_nhds hp))
    refine ⟨T, fun t htS => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hT t hlt.le
    have h2 : p ≤ stdNormalCDF t := htS
    linarith
  have hsub : Sq ⊆ Sp := fun t (ht : q ≤ stdNormalCDF t) => (show p ≤ stdNormalCDF t by linarith)
  have hbddq : BddBelow Sq := hbddp.mono hsub
  have hclosed : IsClosed Sq := isClosed_le continuous_const hc
  have hmem : sInf Sq ∈ Sq := hclosed.csInf_mem hne hbddq
  set b := sInf Sq with hb
  have hqb : q ≤ stdNormalCDF b := hmem
  -- there is t < b with p < Φ t
  have hcb : ContinuousAt stdNormalCDF b := hc.continuousAt
  have hev : ∀ᶠ t in 𝓝 b, p < stdNormalCDF t :=
    hcb.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have ht : p < stdNormalCDF (b - δ / 2) := by
    apply hball
    rw [Real.dist_eq]
    rw [abs_of_neg (by linarith)]
    linarith
  have hle : normalQuantile p ≤ b - δ / 2 := csInf_le hbddp ht.le
  show normalQuantile p < b
  linarith

/-- Key bound: the ratio with `d ≥ 0` is at most `ε`. -/
lemma aux_kz_ratio_le {ε d lam : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) (hl : 0 < lam) :
    entropyRatio ε d lam ≤ ε := by
  unfold entropyRatio
  set t := 1 / lam with ht
  have htpos : 0 < t := by positivity
  have hεl : ε / lam = ε * t := by rw [ht]; field_simp
  rw [hεl]
  have hD : 0 < Real.exp t - 1 := by
    have := Real.add_one_lt_exp htpos.ne'
    linarith
  rw [div_le_iff₀ hD]
  -- convexity: exp (ε t) ≤ ε exp t + (1-ε)
  have hconv := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ 0) hε0.le (by linarith : (0:ℝ) ≤ 1 - ε)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have h1 : Real.exp (ε * t - d) ≤ Real.exp (ε * t) := Real.exp_le_exp.2 (by linarith)
  nlinarith

lemma aux_kz_bdd {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    BddAbove (entropyRatio ε d '' Set.Ioi 0) := by
  refine ⟨ε, ?_⟩
  rintro x ⟨lam, hl, rfl⟩
  exact aux_kz_ratio_le hε0 hε1 hd hl

lemma aux_kz_ne (ε d : ℝ) : (entropyRatio ε d '' Set.Ioi 0).Nonempty :=
  ⟨_, 1, Set.mem_Ioi.2 one_pos, rfl⟩

lemma aux_kz_f_le {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    fEntropy ε d ≤ ε := by
  unfold fEntropy
  apply csSup_le (aux_kz_ne ε d)
  rintro x ⟨lam, hl, rfl⟩
  exact aux_kz_ratio_le hε0 hε1 hd hl

lemma aux_kz_f_pos {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    0 < fEntropy ε d := by
  have hl : 0 < ε / (d + 1) := by positivity
  have hmem : entropyRatio ε d (ε / (d + 1)) ∈ entropyRatio ε d '' Set.Ioi 0 := ⟨_, hl, rfl⟩
  have hle := le_csSup (aux_kz_bdd hε0 hε1 hd) hmem
  have hpos : 0 < entropyRatio ε d (ε / (d + 1)) := by
    unfold entropyRatio
    have e1 : ε / (ε / (d + 1)) - d = 1 := by field_simp; ring
    rw [e1]
    have hn : 0 < Real.exp 1 - 1 := by
      have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
      linarith
    have hpos' : 0 < 1 / (ε / (d + 1)) := by positivity
    have hd' : 0 < Real.exp (1 / (ε / (d + 1))) - 1 := by
      have := Real.add_one_lt_exp hpos'.ne'
      linarith
    exact div_pos hn hd'
  unfold fEntropy
  linarith

/-- `f(ε, d₂) ≤ e^{-(d₂-d₁)} f(ε, d₁)`. -/
lemma aux_kz_f_decay {ε d₁ d₂ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hd₁ : 0 ≤ d₁) (h12 : d₁ ≤ d₂) :
    fEntropy ε d₂ ≤ Real.exp (-(d₂ - d₁)) * fEntropy ε d₁ := by
  unfold fEntropy
  apply csSup_le (aux_kz_ne ε d₂)
  rintro x ⟨lam, hl, rfl⟩
  have hmem : entropyRatio ε d₁ lam ∈ entropyRatio ε d₁ '' Set.Ioi 0 := ⟨_, hl, rfl⟩
  have hle := le_csSup (aux_kz_bdd hε0 hε1 hd₁) hmem
  have hE : 0 ≤ Real.exp (-(d₂ - d₁)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(d₂ - d₁)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have key : entropyRatio ε d₂ lam ≤ Real.exp (-(d₂ - d₁)) * entropyRatio ε d₁ lam := by
    unfold entropyRatio
    have htpos : 0 < 1 / lam := one_div_pos.2 hl
    have hD : 0 < Real.exp (1 / lam) - 1 := by
      have := Real.add_one_lt_exp htpos.ne'
      linarith
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hD.le
    have : Real.exp (-(d₂ - d₁)) * Real.exp (ε / lam - d₁) = Real.exp (ε / lam - d₂) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith
  calc entropyRatio ε d₂ lam ≤ Real.exp (-(d₂ - d₁)) * entropyRatio ε d₁ lam := key
    _ ≤ Real.exp (-(d₂ - d₁)) * sSup (entropyRatio ε d₁ '' Set.Ioi 0) :=
        mul_le_mul_of_nonneg_left hle hE

lemma aux_kz_f_zero {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) : fEntropy ε 0 = ε := by
  unfold fEntropy
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (aux_kz_ne ε 0)
  · rintro x ⟨lam, hl, rfl⟩
    exact aux_kz_ratio_le hε0 hε1 le_rfl hl
  · intro w hw
    set t : ℝ := min 1 ((ε - w) / (2 * ε)) with ht
    have htpos : 0 < t := by
      apply lt_min one_pos
      apply div_pos (by linarith) (by linarith)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ (ε - w) / (2 * ε) := min_le_right _ _
    have ht2' : 2 * ε * t ≤ ε - w := by
      rw [le_div_iff₀ (by linarith)] at ht2
      linarith
    refine ⟨entropyRatio ε 0 (1 / t), ⟨1 / t, Set.mem_Ioi.2 (by positivity), rfl⟩, ?_⟩
    unfold entropyRatio
    have e1 : ε / (1 / t) - 0 = ε * t := by rw [sub_zero]; field_simp
    have e2 : 1 / (1 / t) = t := by field_simp
    rw [e1, e2]
    have hD : 0 < Real.exp t - 1 := by
      have := Real.add_one_lt_exp htpos.ne'
      linarith
    rw [lt_div_iff₀ hD]
    have hN : ε * t + 1 ≤ Real.exp (ε * t) := Real.add_one_le_exp _
    have habs : |Real.exp t - 1 - t| ≤ t ^ 2 := Real.abs_exp_sub_one_sub_id_le (by
      rw [abs_of_pos htpos]; exact ht1)
    have hup : Real.exp t - 1 ≤ t + t ^ 2 := by
      have := (abs_le.1 habs).2
      linarith
    rcases le_or_gt w 0 with hw0 | hw0
    · have : w * (Real.exp t - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw0 hD.le
      have : 0 < ε * t := by positivity
      linarith
    · have h1 : w * (Real.exp t - 1) ≤ w * (t + t ^ 2) := mul_le_mul_of_nonneg_left hup hw0.le
      -- w (t + t^2) < ε t
      have h2 : w * (t + t ^ 2) < ε * t := by
        have : w * t ≤ ε * t := mul_le_mul_of_nonneg_right hw.le htpos.le
        nlinarith
      linarith

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    fEntropy ε 0 = ε ∧ kappaEntropy ε 0 = -normalQuantile ε ∧
      StrictMonoOn (kappaEntropy ε) (Set.Ici 0) := by
  have h0 := aux_kz_f_zero hε0 hε1
  refine ⟨h0, ?_, ?_⟩
  · unfold kappaEntropy; rw [h0]
  · intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    unfold kappaEntropy
    have hfa_le := aux_kz_f_le hε0 hε1 ha
    have hfb_pos := aux_kz_f_pos hε0 hε1 hb
    have hfa_pos := aux_kz_f_pos hε0 hε1 ha
    have hdec := aux_kz_f_decay hε0 hε1 ha hab.le
    have hE1 : Real.exp (-(b - a)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have hlt : fEntropy ε b < fEntropy ε a := by nlinarith
    have := aux_kz_quant hfb_pos hlt (by linarith)
    linarith
