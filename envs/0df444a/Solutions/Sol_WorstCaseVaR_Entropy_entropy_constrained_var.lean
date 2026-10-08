-- Prove2me | solution 1 for WorstCaseVaR.Entropy.entropy_constrained_var
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T23:27:38.076555+00:00
-- url     : https://prove2.me/submissions/f7b36f5a-eddf-4c32-a049-a45a4bc9cc35

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

set_option autoImplicit false

/- Complete checked body: AttributedEntropy -/
section


/- Complete attributed source: kappa_at_zero -/
section
-- Prove2me | solution 1 for WorstCaseVaR.Entropy.kappa_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:18:48.952296+00:00
-- url     : https://prove2.me/submissions/a6d140dd-5861-46a0-908d-298a1b865811


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

theorem entropy_kappa_zero_checked (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
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

end

/- Complete attributed source: worst_case_probability_dual -/
section
-- Prove2me | solution 1 for WorstCaseVaR.Entropy.worst_case_probability_dual
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:05:42.064992+00:00
-- url     : https://prove2.me/submissions/c3cdd3a4-e57d-4ee9-beb5-42cf1659b5c5


namespace WorstCaseVaR.Entropy

open MeasureTheory ProbabilityTheory InformationTheory

lemma aux_wcv_weak {α : Type*} [MeasurableSpace α] (P₀ P : Measure α) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P] {S : Set α} (hS : MeasurableSet S) {d : ℝ} (hd : 0 ≤ d)
    (hP : klDiv P P₀ ≤ ENNReal.ofReal d) (t : ℝ) :
    t * P.real S ≤ d + Real.log ((Real.exp t - 1) * P₀.real S + 1) := by
  have hne : klDiv P P₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hP
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hne
  have hKL : ∫ x, llr P P₀ x ∂P ≤ d := by
    have h1 := toReal_klDiv hac hint
    simp only [probReal_univ, add_sub_cancel_right] at h1
    rw [← h1]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rwa [ENNReal.toReal_ofReal hd] at this
  set f : α → ℝ := S.indicator (fun _ => t) with hf_def
  have hexp : (fun x => Real.exp (f x)) = fun x => S.indicator (fun _ => Real.exp t - 1) x + 1 := by
    funext x
    by_cases hx : x ∈ S <;> simp [f, hx]
  have hexp_int : Integrable (fun x => Real.exp (f x)) P₀ := by
    rw [hexp]
    exact ((integrable_const _).indicator hS).add (integrable_const _)
  have hexp_integral : ∫ x, Real.exp (f x) ∂P₀ = (Real.exp t - 1) * P₀.real S + 1 := by
    rw [hexp, integral_add ((integrable_const _).indicator hS) (integrable_const _),
      integral_indicator_const _ hS]
    simp [smul_eq_mul, mul_comm]
  have hf_int : Integrable f P := (integrable_const t).indicator hS
  have hf_integral : ∫ x, f x ∂P = t * P.real S := by
    rw [hf_def, integral_indicator_const _ hS, smul_eq_mul, mul_comm]
  have : IsProbabilityMeasure (P₀.tilted f) := isProbabilityMeasure_tilted hexp_int
  have hacQ : P ≪ P₀.tilted f := hac.trans (absolutelyContinuous_tilted hexp_int)
  have hintQ : Integrable (llr P (P₀.tilted f)) P :=
    integrable_llr_tilted_right hac hf_int hint hexp_int
  have hG := integral_llr_add_sub_measure_univ_nonneg hacQ hintQ
  rw [integral_llr_tilted_right hac hf_int hexp_int hint] at hG
  simp only [probReal_univ, add_sub_cancel_right] at hG
  rw [hf_integral, hexp_integral] at hG
  linarith

lemma aux_wcv_primal {α : Type*} [MeasurableSpace α] (P₀ : Measure α) [IsProbabilityMeasure P₀]
    {S : Set α} (hS : MeasurableSet S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * P₀.real S + b * (1 - P₀.real S) = 1) :
    ∃ P : Measure α, IsProbabilityMeasure P ∧
      klDiv P P₀ = ENNReal.ofReal (P₀.real S * klFun a + (1 - P₀.real S) * klFun b) ∧
      P.real S = a * P₀.real S := by
  classical
  set φ := P₀.real S with hφ
  have hφ0 : 0 ≤ φ := measureReal_nonneg
  have hφ1 : φ ≤ 1 := measureReal_le_one
  have hPS : P₀ S = ENNReal.ofReal φ := by rw [hφ, ofReal_measureReal]
  have hPSc : P₀ Sᶜ = ENNReal.ofReal (1 - φ) := by
    rw [← ofReal_measureReal, probReal_compl_eq_one_sub hS]
  let h : α → ENNReal := S.piecewise (fun _ => ENNReal.ofReal a) (fun _ => ENNReal.ofReal b)
  have hm : Measurable h := Measurable.piecewise hS measurable_const measurable_const
  have hlin : ∀ g : ENNReal → ENNReal,
      ∫⁻ x, g (h x) ∂P₀ = g (ENNReal.ofReal a) * ENNReal.ofReal φ
        + g (ENNReal.ofReal b) * ENNReal.ofReal (1 - φ) := by
    intro g
    rw [← lintegral_add_compl _ hS]
    have e1 : ∫⁻ x in S, g (h x) ∂P₀ = ∫⁻ x in S, g (ENNReal.ofReal a) ∂P₀ :=
      setLIntegral_congr_fun hS (fun x hx => by simp [h, hx])
    have e2 : ∫⁻ x in Sᶜ, g (h x) ∂P₀ = ∫⁻ x in Sᶜ, g (ENNReal.ofReal b) ∂P₀ :=
      setLIntegral_congr_fun hS.compl (fun x hx => by simp [h, Set.notMem_of_mem_compl hx])
    rw [e1, e2, setLIntegral_const, setLIntegral_const, hPS, hPSc]
  have huniv : P₀.withDensity h Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have := hlin id
    simp only [id] at this
    rw [this, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
      ← ENNReal.ofReal_add (mul_nonneg ha hφ0) (mul_nonneg hb (by linarith)), hab,
      ENNReal.ofReal_one]
  have hprob : IsProbabilityMeasure (P₀.withDensity h) := ⟨huniv⟩
  refine ⟨P₀.withDensity h, hprob, ?_, ?_⟩
  · rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous P₀ h)]
    have hae : (fun x => ENNReal.ofReal (klFun ((P₀.withDensity h).rnDeriv P₀ x).toReal))
        =ᵐ[P₀] fun x => ENNReal.ofReal (klFun (h x).toReal) := by
      filter_upwards [Measure.rnDeriv_withDensity P₀ hm] with x hx
      rw [hx]
    rw [lintegral_congr_ae hae, hlin (fun y => ENNReal.ofReal (klFun y.toReal))]
    simp only [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
    rw [← ENNReal.ofReal_mul (klFun_nonneg ha), ← ENNReal.ofReal_mul (klFun_nonneg hb),
      ← ENNReal.ofReal_add (mul_nonneg (klFun_nonneg ha) hφ0)
        (mul_nonneg (klFun_nonneg hb) (by linarith))]
    congr 1
    ring
  · rw [measureReal_def, withDensity_apply _ hS]
    have e1 : ∫⁻ x in S, h x ∂P₀ = ∫⁻ x in S, ENNReal.ofReal a ∂P₀ :=
      setLIntegral_congr_fun hS (fun x hx => by simp [h, hx])
    rw [e1, setLIntegral_const, hPS, ← ENNReal.ofReal_mul ha, ENNReal.toReal_ofReal (mul_nonneg ha hφ0)]

lemma aux_wcv_sandwich (A B : Set ℝ)
    (hle : ∀ a ∈ A, ∀ b ∈ B, a ≤ b)
    (happrox : ∀ ε > 0, ∃ a ∈ A, ∃ b ∈ B, b < a + ε) :
    ∃ θ, IsLUB A θ ∧ IsGLB B θ := by
  obtain ⟨a0, ha0, b0, hb0, -⟩ := happrox 1 one_pos
  have hA : A.Nonempty := ⟨a0, ha0⟩
  have hbdd : BddAbove A := ⟨b0, fun a ha => hle a ha b0 hb0⟩
  refine ⟨sSup A, isLUB_csSup hA hbdd, ?_, ?_⟩
  · intro b hb
    exact csSup_le hA (fun a ha => hle a ha b hb)
  · intro c hc
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    obtain ⟨a, ha, b, hb, hlt⟩ := happrox ε hε
    have h1 : c ≤ b := hc hb
    have h2 : a ≤ sSup A := le_csSup hbdd ha
    linarith

lemma aux_wcv_scalar {φ d ε : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a * φ + b * (1 - φ) = 1 ∧
      φ * klFun a + (1 - φ) * klFun b ≤ d ∧
      ∃ lam : ℝ, 0 < lam ∧ dualValue d φ lam < a * φ + ε := by
  rcases eq_or_lt_of_le hφ0 with hφ | hφpos
  · -- φ = 0
    subst hφ
    refine ⟨1, 1, zero_le_one, zero_le_one, by ring, by simp [klFun_one]; exact hd, ε / (d + 1),
      by positivity, ?_⟩
    simp only [dualValue, mul_zero, zero_add, Real.log_one, add_zero]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  by_cases hB : -Real.log φ ≤ d
  · -- the conditional measure is feasible
    refine ⟨1 / φ, 0, by positivity, le_refl _, by field_simp; ring, ?_, ε / (d + 1),
      by positivity, ?_⟩
    · simp only [klFun_apply, Real.log_zero, mul_zero, zero_add, sub_zero, mul_one]
      rw [one_div, Real.log_inv]
      field_simp
      linarith
    · have hlam : 0 < ε / (d + 1) := by positivity
      set lam := ε / (d + 1) with hlam_def
      have he : 1 ≤ Real.exp (1 / lam) := Real.one_le_exp (by positivity)
      have hlog : Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ 1 / lam := by
        calc Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ Real.log (Real.exp (1 / lam)) := by
              apply Real.log_le_log (by nlinarith)
              nlinarith
          _ = 1 / lam := Real.log_exp _
      have h1 : lam * Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ 1 := by
        calc lam * Real.log ((Real.exp (1 / lam) - 1) * φ + 1) ≤ lam * (1 / lam) :=
              mul_le_mul_of_nonneg_left hlog hlam.le
          _ = 1 := by field_simp
      have h2 : lam * d < ε := by
        rw [hlam_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
      have h3 : 1 / φ * φ = 1 := by field_simp
      simp only [dualValue]
      rw [h3]
      linarith
  push Not at hB
  have hφlt : φ < 1 := by
    have : Real.log φ < 0 := by linarith
    exact (Real.log_neg_iff hφpos).mp this
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · -- d = 0: the reference measure, λ → ∞
    subst hd0
    refine ⟨1, 1, zero_le_one, zero_le_one, by ring, by simp [klFun_one], ?_⟩
    have hL : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    set s := Real.log (1 + ε) / 2 with hs_def
    have hs : 0 < s := by positivity
    have hes : Real.exp s < 1 + ε := by
      calc Real.exp s < Real.exp (Real.log (1 + ε)) := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 + ε := Real.exp_log (by linarith)
    refine ⟨1 / s, by positivity, ?_⟩
    simp only [dualValue, mul_zero, zero_add, one_div_one_div, one_mul]
    have he1 : 1 ≤ Real.exp s := Real.one_le_exp hs.le
    have hpos : 0 < (Real.exp s - 1) * φ + 1 := by nlinarith
    have hl := Real.log_le_sub_one_of_pos hpos
    -- e^s - 1 ≤ s e^s
    have hkey : Real.exp s - 1 ≤ s * Real.exp s := by
      have := Real.add_one_le_exp (-s)
      have hmul : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos s]
    have h1 : 1 / s * Real.log ((Real.exp s - 1) * φ + 1) ≤ 1 / s * ((Real.exp s - 1) * φ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : 1 / s * ((Real.exp s - 1) * φ) ≤ Real.exp s * φ := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs]
      nlinarith
    nlinarith
  · -- interior case: intermediate value theorem
    set F : ℝ → ℝ := fun p => p * Real.log p + (1 - p) * Real.log (1 - p)
      - p * Real.log φ - (1 - p) * Real.log (1 - φ) with hF
    have hFc : Continuous F := by
      have h1 : Continuous fun p : ℝ => p * Real.log p := Real.continuous_mul_log
      have h2 : Continuous fun p : ℝ => (1 - p) * Real.log (1 - p) :=
        Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
      exact ((h1.add h2).sub (continuous_id.mul continuous_const)).sub
        ((continuous_const.sub continuous_id).mul continuous_const)
    have hFφ : F φ = 0 := by simp only [hF]; ring
    have hF1 : F 1 = -Real.log φ := by simp [hF]
    have hmem : d ∈ Set.Icc (F φ) (F 1) := ⟨by rw [hFφ]; exact hd, by rw [hF1]; exact hB.le⟩
    obtain ⟨p, ⟨hpφ, hp1⟩, hFp⟩ := intermediate_value_Icc hφlt.le hFc.continuousOn hmem
    have hpφ' : φ < p := by
      rcases eq_or_lt_of_le hpφ with h | h
      · subst h; rw [hFφ] at hFp; linarith
      · exact h
    have hp1' : p < 1 := by
      rcases eq_or_lt_of_le hp1 with h | h
      · subst h; rw [hF1] at hFp; linarith
      · exact h
    have hp0 : 0 < p := by linarith
    have h1p : 0 < 1 - p := by linarith
    have h1φ : 0 < 1 - φ := by linarith
    refine ⟨p / φ, (1 - p) / (1 - φ), by positivity, by positivity, by field_simp; ring, ?_, ?_⟩
    · simp only [klFun_apply]
      rw [Real.log_div hp0.ne' hφpos.ne', Real.log_div h1p.ne' h1φ.ne']
      have : F p = d := hFp
      simp only [hF] at this
      field_simp
      linarith
    · set t := Real.log p + Real.log (1 - φ) - Real.log φ - Real.log (1 - p) with ht
      have htpos : 0 < t := by
        have := Real.log_lt_log hφpos hpφ'
        have := Real.log_lt_log h1p (show 1 - p < 1 - φ by linarith)
        linarith
      refine ⟨1 / t, by positivity, ?_⟩
      have het : Real.exp t = p * (1 - φ) / (φ * (1 - p)) := by
        rw [ht, Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log hp0, Real.exp_log h1φ,
          Real.exp_log hφpos, Real.exp_log h1p]
        field_simp
      have harg : (Real.exp t - 1) * φ + 1 = (1 - φ) / (1 - p) := by
        rw [het]
        field_simp
        ring
      simp only [dualValue, one_div_one_div]
      rw [harg, Real.log_div h1φ.ne' h1p.ne']
      have : F p = d := hFp
      simp only [hF] at this
      have hval : 1 / t * d + 1 / t * (Real.log (1 - φ) - Real.log (1 - p)) = p := by
        rw [← mul_add, ← this]
        field_simp
        rw [ht]
        ring
      rw [hval]
      have : p / φ * φ = p := by field_simp
      rw [this]
      linarith


lemma aux_wcv_main {α : Type*} [MeasurableSpace α] (P₀ : Measure α) [IsProbabilityMeasure P₀]
    {S : Set α} (hS : MeasurableSet S) {d : ℝ} (hd : 0 ≤ d) (ball : Set (Measure α))
    (hball : ∀ P, P ∈ ball ↔ (IsProbabilityMeasure P ∧ klDiv P P₀ ≤ ENNReal.ofReal d)) :
    ∃ θ : ℝ, IsLUB {p | ∃ P ∈ ball, P.real S = p} θ ∧
      IsGLB (dualValue d (P₀.real S) '' Set.Ioi 0) θ := by
  apply aux_wcv_sandwich
  · rintro a ⟨P, hPb, rfl⟩ b ⟨lam, hlam, rfl⟩
    obtain ⟨hPprob, hPkl⟩ := (hball P).mp hPb
    have hlam' : (0 : ℝ) < lam := hlam
    have h := aux_wcv_weak P₀ P hS hd hPkl (1 / lam)
    have h2 : lam * (1 / lam * P.real S) ≤ lam * (d + Real.log ((Real.exp (1 / lam) - 1) * P₀.real S + 1)) :=
      mul_le_mul_of_nonneg_left h hlam'.le
    have h3 : lam * (1 / lam * P.real S) = P.real S := by field_simp
    simp only [dualValue]
    linarith
  · intro ε hε
    have hφ0 : 0 ≤ P₀.real S := measureReal_nonneg
    have hφ1 : P₀.real S ≤ 1 := measureReal_le_one
    obtain ⟨a, b, ha, hb, hab, hkl, lam, hlam, hlt⟩ := aux_wcv_scalar hφ0 hφ1 hd hε
    obtain ⟨P, hPprob, hPkl, hPS⟩ := aux_wcv_primal P₀ hS ha hb hab
    refine ⟨a * P₀.real S, ⟨P, (hball P).mpr ⟨hPprob, ?_⟩, hPS⟩, dualValue d (P₀.real S) lam,
      ⟨lam, hlam, rfl⟩, hlt⟩
    rw [hPkl]
    exact ENNReal.ofReal_le_ofReal hkl

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy

theorem entropy_dual_checked {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (_hΓ : Γ.PosDef) (_hw : w ≠ 0) (d : ℝ) (hd : 0 ≤ d) (γ : ℝ) :
    ∃ θ : ℝ,
      IsLUB {p | ∃ P ∈ klBall xhat Γ d, P.real (lossSet w γ) = p} θ ∧
      IsGLB (dualValue d ((refGaussian xhat Γ).real (lossSet w γ)) '' Set.Ioi 0) θ := by
  have hprob : MeasureTheory.IsProbabilityMeasure (refGaussian xhat Γ) := by
    unfold refGaussian; infer_instance
  have hS : MeasurableSet (lossSet w γ) := by
    unfold lossSet
    exact measurableSet_le measurable_const (by fun_prop)
  exact aux_wcv_main (refGaussian xhat Γ) hS hd (klBall xhat Γ d) (fun P => Iff.rfl)

end

/- Complete attributed source: gaussian_tail_eq -/
section
-- Prove2me | solution 1 for WorstCaseVaR.Entropy.gaussian_tail_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:54:57.528115+00:00
-- url     : https://prove2.me/submissions/2e8a33d4-65b9-4c44-8b59-c0decea2b0e6


namespace WorstCaseVaR.Entropy
open MeasureTheory ProbabilityTheory

theorem aux_gte_cov {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) : covarianceBilin (multivariateGaussian xhat Γ) w w = quadForm Γ w := by
  rw [covarianceBilin_multivariateGaussian hΓ.posSemidef]
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_gte_pos {n : ℕ} (w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) : 0 < quadForm Γ w := by
  have h := hΓ.dotProduct_mulVec_pos (x := w.ofLp) (by simpa using hw)
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_trivial] at h
  refine lt_of_lt_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_gte_quad_neg {n : ℕ} (w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ) :
    quadForm Γ (-w) = quadForm Γ w := by
  unfold quadForm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp

theorem aux_gte_map {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) :
    (multivariateGaussian xhat Γ).map (innerSL ℝ w) =
      gaussianReal (inner ℝ w xhat) (quadForm Γ w).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal]
  congr 1
  · rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id]
    simp
  · rw [← aux_gte_cov xhat w Γ hΓ, covarianceBilin_self IsGaussian.memLp_two_id]
    rfl

/-- standardization -/
theorem aux_gte_std (m : ℝ) (v : ℝ) (hv : 0 < v) (γ : ℝ) :
    (gaussianReal m v.toNNReal).real (Set.Ici γ) =
      1 - cdf (gaussianReal 0 1) ((γ - m) / Real.sqrt v) := by
  have hσ : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hrep : gaussianReal m v.toNNReal =
      (gaussianReal 0 1).map (fun x => Real.sqrt v * x + m) := by
    have : (fun x => Real.sqrt v * x + m) = (· + m) ∘ (Real.sqrt v * ·) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt hv.le, hv.le]
  rw [hrep, map_measureReal_apply (by fun_prop) measurableSet_Ici]
  have hpre : (fun x => Real.sqrt v * x + m) ⁻¹' Set.Ici γ = Set.Ici ((γ - m) / Real.sqrt v) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici]
    rw [div_le_iff₀ hσ]
    constructor <;> intro h <;> linarith
  rw [hpre, cdf_eq_real]
  have := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (v := 1) one_ne_zero
  rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr Iio_ae_eq_Iic]

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy
open MeasureTheory ProbabilityTheory

theorem entropy_gaussian_tail_checked {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (γ : ℝ) :
    (refGaussian xhat Γ).real (lossSet w γ) = gaussianTail xhat Γ w γ := by
  have hset : lossSet w γ = (innerSL ℝ (-w)) ⁻¹' Set.Ici γ := by
    ext x
    simp [lossSet, real_inner_comm]
  rw [refGaussian, hset, ← map_measureReal_apply (by fun_prop) measurableSet_Ici,
    aux_gte_map xhat (-w) Γ hΓ, aux_gte_quad_neg,
    aux_gte_std _ _ (aux_gte_pos w Γ hΓ hw), gaussianTail, stdNormalCDF]
  congr 2
  simp [inner_neg_left]

end

/- Complete attributed source: fEntropy_two_expressions -/
section
-- Prove2me | solution 1 for WorstCaseVaR.Entropy.fEntropy_two_expressions
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:44:19.072918+00:00
-- url     : https://prove2.me/submissions/e5964cd5-3f1c-44af-b8ab-c8848d6c914c


namespace WorstCaseVaR.Entropy

theorem aux_fE2_image_eq (ε d : ℝ) :
    entropyRatio ε d '' Set.Ioi 0 =
      (fun v : ℝ => (Real.exp (-d) * (v + 1) ^ ε - 1) / v) '' Set.Ioi 0 := by
  ext y
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨lam, hlam, rfl⟩
    refine ⟨Real.exp (1 / lam) - 1, ?_, ?_⟩
    · have : 1 < Real.exp (1 / lam) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    · unfold entropyRatio
      simp only [sub_add_cancel]
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 3
      ring
  · rintro ⟨v, hv, rfl⟩
    have hlog : 0 < Real.log (v + 1) := Real.log_pos (by linarith)
    refine ⟨1 / Real.log (v + 1), by positivity, ?_⟩
    unfold entropyRatio
    have hv1 : 0 < v + 1 := by linarith
    rw [one_div_one_div, Real.exp_log hv1, Real.rpow_def_of_pos hv1, ← Real.exp_add]
    congr 3
    · field_simp
      ring
    · ring

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy

theorem entropy_two_expressions_checked (ε d : ℝ) :
    fEntropy ε d =
      sSup ((fun v : ℝ => (Real.exp (-d) * (v + 1) ^ ε - 1) / v) '' Set.Ioi 0) := by
  unfold fEntropy
  rw [aux_fE2_image_eq]

end
end

/- Complete checked body: ScalarRegularity -/
section

set_option autoImplicit false
open Set Filter Topology WorstCaseVaR.Entropy

namespace WorstCaseVaR.EntropyProof

theorem entropyRatio_convex (d lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ Set.univ (fun ε : ℝ => entropyRatio ε d lam) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hD : 0 < Real.exp (1 / lam) - 1 := by
    have ht : 0 < 1 / lam := by positivity
    linarith [Real.add_one_lt_exp ht.ne']
  have he := convexOn_exp.2 (Set.mem_univ (x/lam-d)) (Set.mem_univ (y/lam-d)) ha hb hab
  simp only [smul_eq_mul] at he ⊢
  have haff : (a*x+b*y)/lam-d = a*(x/lam-d)+b*(y/lam-d) := by
    linear_combination d * hab
  rw [← haff] at he
  unfold entropyRatio
  calc
    _ ≤ (a*(Real.exp (x/lam-d)-1)+b*(Real.exp (y/lam-d)-1)) /
        (Real.exp (1/lam)-1) := div_le_div_of_nonneg_right (by linarith) hD.le
    _ = _ := by ring

theorem entropyRatio_zero_le (d lam : ℝ) (hd : 0 ≤ d) (hlam : 0 < lam) :
    entropyRatio 0 d lam ≤ 0 := by
  unfold entropyRatio
  apply div_nonpos_of_nonpos_of_nonneg
  · simp only [zero_div, zero_sub]
    exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by linarith))
  · exact sub_nonneg.mpr (Real.one_le_exp (by positivity))

/-- The supremum is taken only in its finite regime; no claim is made for ε>1. -/
theorem fEntropy_convex (d : ℝ) (hd : 0 ≤ d) :
    ConvexOn ℝ (Set.Ioo (0 : ℝ) 1) (fun ε => fEntropy ε d) := by
  refine ⟨convex_Ioo 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  change sSup (entropyRatio (a*x+b*y) d '' Set.Ioi 0) ≤ _
  apply csSup_le (aux_kz_ne _ _)
  rintro _ ⟨lam, hlam, rfl⟩
  have hc := (entropyRatio_convex d lam hlam).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hc
  have hxle : entropyRatio x d lam ≤ fEntropy x d :=
    le_csSup (aux_kz_bdd hx.1 hx.2 hd) ⟨lam, hlam, rfl⟩
  have hyle : entropyRatio y d lam ≤ fEntropy y d :=
    le_csSup (aux_kz_bdd hy.1 hy.2 hd) ⟨lam, hlam, rfl⟩
  exact hc.trans (add_le_add (mul_le_mul_of_nonneg_left hxle ha)
    (mul_le_mul_of_nonneg_left hyle hb))

theorem fEntropy_continuous (d : ℝ) (hd : 0 ≤ d) :
    ContinuousOn (fun ε => fEntropy ε d) (Set.Ioo (0 : ℝ) 1) :=
  (fEntropy_convex d hd).continuousOn isOpen_Ioo

theorem fEntropy_scaling {ε ε' d : ℝ} (hε : 0 < ε) (hε' : ε < ε')
    (hε'1 : ε' < 1) (hd : 0 ≤ d) :
    fEntropy ε d ≤ (ε/ε') * fEntropy ε' d := by
  have hp : 0 < ε' := hε.trans hε'
  have ha : 0 ≤ ε/ε' := by positivity
  have hb : 0 ≤ 1-ε/ε' := by
    have := (div_lt_one hp).mpr hε'
    linarith
  change sSup (entropyRatio ε d '' Set.Ioi 0) ≤ _
  apply csSup_le (aux_kz_ne _ _)
  rintro _ ⟨lam, hlam, rfl⟩
  have hc := (entropyRatio_convex d lam hlam).2 (Set.mem_univ ε') (Set.mem_univ 0)
    ha hb (by ring : ε/ε'+(1-ε/ε')=1)
  have he : (ε/ε')*ε'+(1-ε/ε')*0 = ε := by field_simp; ring
  simp only [smul_eq_mul] at hc
  rw [he] at hc
  have hzero := entropyRatio_zero_le d lam hd hlam
  have hup : entropyRatio ε' d lam ≤ fEntropy ε' d :=
    le_csSup (aux_kz_bdd hp hε'1 hd) ⟨lam, hlam, rfl⟩
  have hmul := mul_le_mul_of_nonneg_left hup ha
  have hneg := mul_nonpos_of_nonneg_of_nonpos hb hzero
  linarith

theorem fEntropy_strictMono (d : ℝ) (hd : 0 ≤ d) :
    StrictMonoOn (fun ε => fEntropy ε d) (Set.Ioo (0 : ℝ) 1) := by
  intro ε hε ε' hε' hlt
  have hs := fEntropy_scaling hε.1 hlt hε'.2 hd
  have hp := aux_kz_f_pos hε'.1 hε'.2 hd
  have hr : ε/ε' < 1 := (div_lt_one hε'.1).mpr hlt
  have hm := mul_lt_mul_of_pos_right hr hp
  simpa only [one_mul] using hs.trans_lt hm

end WorstCaseVaR.EntropyProof

end

/- Complete checked body: ScalarThreshold -/
section

set_option autoImplicit false
open Set Filter Topology WorstCaseVaR.Entropy

namespace WorstCaseVaR.EntropyProof

theorem dual_lt_iff_ratio {q ε d lam : ℝ} (hq : 0 ≤ q) (hlam : 0 < lam) :
    dualValue d q lam < ε ↔ q < entropyRatio ε d lam := by
  have hD : 0 < Real.exp (1/lam)-1 := by
    have ht : 0 < 1/lam := by positivity
    linarith [Real.add_one_lt_exp ht.ne']
  have harg : 0 < (Real.exp (1/lam)-1)*q+1 := by positivity
  have hmul : lam*(ε/lam)=ε := mul_div_cancel₀ _ hlam.ne'
  constructor
  · intro h
    have hlog : Real.log ((Real.exp (1/lam)-1)*q+1) < ε/lam-d := by
      unfold dualValue at h
      nlinarith
    have he := (Real.log_lt_iff_lt_exp harg).mp hlog
    exact (lt_div_iff₀ hD).mpr (by nlinarith)
  · intro h
    have he := (lt_div_iff₀ hD).mp h
    have hlog := (Real.log_lt_iff_lt_exp harg).mpr (by nlinarith :
      (Real.exp (1/lam)-1)*q+1 < Real.exp (ε/lam-d))
    unfold dualValue
    nlinarith

theorem dual_glb_lt_iff {q ε d θ : ℝ} (hq : 0 ≤ q)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d)
    (hθ : IsGLB (dualValue d q '' Set.Ioi 0) θ) :
    θ < ε ↔ q < fEntropy ε d := by
  have hglb : θ < ε ↔ ∃ v ∈ dualValue d q '' Set.Ioi 0, v < ε := by
    constructor
    · intro h
      by_contra hn
      push Not at hn
      have hh := hθ.2 hn
      linarith
    · rintro ⟨v, hv, hve⟩
      exact (hθ.1 hv).trans_lt hve
  rw [hglb, fEntropy, lt_csSup_iff (aux_kz_bdd hε0 hε1 hd) (aux_kz_ne ε d)]
  constructor
  · rintro ⟨_, ⟨lam, hlam, rfl⟩, hlt⟩
    exact ⟨_, ⟨lam, hlam, rfl⟩, (dual_lt_iff_ratio hq hlam).mp hlt⟩
  · rintro ⟨_, ⟨lam, hlam, rfl⟩, hlt⟩
    exact ⟨_, ⟨lam, hlam, rfl⟩, (dual_lt_iff_ratio hq hlam).mpr hlt⟩

/-- Boundary completion by the risk function's interior regularity, including d=0. -/
theorem dual_glb_le_iff {q ε d θ : ℝ} (hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d)
    (hθ : IsGLB (dualValue d q '' Set.Ioi 0) θ) :
    θ ≤ ε ↔ q ≤ fEntropy ε d := by
  constructor
  · intro hle
    by_contra hq
    have hqgt : fEntropy ε d < q := lt_of_not_ge hq
    have hc : ContinuousAt (fun e => fEntropy e d) ε :=
      (fEntropy_continuous d hd).continuousAt (isOpen_Ioo.mem_nhds ⟨hε0,hε1⟩)
    have hev : ∀ᶠ e in 𝓝 ε, fEntropy e d < q ∧ e < 1 :=
      (hc.eventually (gt_mem_nhds hqgt)).and (Iio_mem_nhds hε1)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hdist : dist (ε+δ/2) ε < δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity : 0 < δ/2)]
      linarith
    obtain ⟨hf, he1⟩ := hball hdist
    have he0 : 0 < ε+δ/2 := by linarith
    have hθe : θ < ε+δ/2 := by linarith
    have hbad := (dual_glb_lt_iff hq0 he0 he1 hd hθ).mp hθe
    linarith
  · intro hq
    by_contra hle
    have ht : ε < θ := lt_of_not_ge hle
    obtain ⟨e, he, hemin⟩ := exists_between (lt_min ht hε1)
    have he0 : 0 < e := hε0.trans he
    have he1 : e < 1 := hemin.trans_le (min_le_right _ _)
    have het : e < θ := hemin.trans_le (min_le_left _ _)
    have hf := fEntropy_strictMono d hd ⟨hε0,hε1⟩ ⟨he0,he1⟩ he
    have hθe := (dual_glb_lt_iff hq0 he0 he1 hd hθ).mpr (hq.trans_lt hf)
    linarith

end WorstCaseVaR.EntropyProof

end

/- Complete checked body: ProbabilityThreshold -/
section

namespace WorstCaseVaR.EntropyProof
open WorstCaseVaR.Entropy MeasureTheory ProbabilityTheory Set

theorem varFeasible_iff_tail {n : ℕ} (xhat w : Returns n)
    (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef) (hw : w ≠ 0)
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) (γ : ℝ) :
    γ ∈ varFeasible (klBall xhat Γ d) w ε ↔
      gaussianTail xhat Γ w γ ≤ fEntropy ε d := by
  obtain ⟨θ, hupper, hlower⟩ := entropy_dual_checked xhat w Γ hΓ hw d hd γ
  have : IsProbabilityMeasure (refGaussian xhat Γ) := by
    unfold refGaussian
    infer_instance
  have hθ : θ ≤ ε ↔ (refGaussian xhat Γ).real (lossSet w γ) ≤ fEntropy ε d :=
    dual_glb_le_iff measureReal_nonneg measureReal_le_one hε0 hε1 hd hlower
  rw [entropy_gaussian_tail_checked xhat w Γ hΓ hw γ] at hθ
  rw [← hθ, isLUB_le_iff hupper]
  constructor
  · intro h p hp
    obtain ⟨P, hP, rfl⟩ := hp
    have : IsProbabilityMeasure P := hP.1
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε0.le).mp (h P hP)
  · intro h P hP
    have : IsProbabilityMeasure P := hP.1
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε0.le).mpr
    exact h ⟨P, hP, rfl⟩

end WorstCaseVaR.EntropyProof

end

/- Complete checked body: NormalCDF -/
section

namespace WorstCaseVaR.EntropyProof
open WorstCaseVaR.Entropy MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem stdNormalCDF_strictMono : StrictMono stdNormalCDF := by
  intro a b hab
  by_contra hn
  have hle : stdNormalCDF b ≤ stdNormalCDF a := le_of_not_gt hn
  have hzero : gaussianReal 0 1 (Ioc a b) = 0 := by
    have hh := (cdf (gaussianReal 0 1)).measure_Ioc a b
    rw [measure_cdf] at hh
    exact hh.trans (ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hle))
  have hz := gaussianReal_absolutelyContinuous' (0 : ℝ) (by norm_num : (1 : ℝ≥0) ≠ 0) hzero
  have hp : (0 : ℝ≥0∞) < volume (Ioc a b) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact hp.ne' hz

theorem stdNormalCDF_pos (t : ℝ) : 0 < stdNormalCDF t := by
  have hh := stdNormalCDF_strictMono (show t - 1 < t by linarith)
  have hz : 0 ≤ stdNormalCDF (t - 1) := cdf_nonneg _ _
  linarith

theorem stdNormalCDF_lt_one (t : ℝ) : stdNormalCDF t < 1 := by
  have hh := stdNormalCDF_strictMono (show t < t + 1 by linarith)
  have hz : stdNormalCDF (t + 1) ≤ 1 := cdf_le_one _ _
  linarith

theorem stdNormalCDF_surj {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ t : ℝ, stdNormalCDF t = p := by
  have hl : Tendsto stdNormalCDF atBot (𝓝 0) := tendsto_cdf_atBot _
  have hr : Tendsto stdNormalCDF atTop (𝓝 1) := tendsto_cdf_atTop _
  obtain ⟨a, ha⟩ := (hl.eventually (gt_mem_nhds hp)).exists
  obtain ⟨b, hb⟩ := (hr.eventually (lt_mem_nhds hp1)).exists
  exact intermediate_value_univ a b WorstCaseVaR.Entropy.aux_kz_cont ⟨ha.le, hb.le⟩

theorem normalQuantile_cdf (t : ℝ) : normalQuantile (stdNormalCDF t) = t := by
  have hs : {a : ℝ | stdNormalCDF t ≤ stdNormalCDF a} = Ici t := by
    ext a
    exact stdNormalCDF_strictMono.le_iff_le
  rw [normalQuantile, hs, csInf_Ici]

theorem cdf_normalQuantile {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    stdNormalCDF (normalQuantile p) = p := by
  obtain ⟨t, rfl⟩ := stdNormalCDF_surj hp hp1
  rw [normalQuantile_cdf]

theorem cdf_le_iff_le_quantile {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (t : ℝ) :
    stdNormalCDF t ≤ p ↔ t ≤ normalQuantile p := by
  calc
    stdNormalCDF t ≤ p ↔ stdNormalCDF t ≤ stdNormalCDF (normalQuantile p) := by
      rw [cdf_normalQuantile hp hp1]
    _ ↔ t ≤ normalQuantile p := stdNormalCDF_strictMono.le_iff_le

theorem stdNormalCDF_neg (t : ℝ) : stdNormalCDF (-t) = 1 - stdNormalCDF t := by
  let μ := gaussianReal (0 : ℝ) (1 : ℝ≥0)
  have hm : μ.map (fun x => -x) = μ := by simpa [μ] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have he : μ (Iic (-t)) = μ (Ici t) := by
    calc
      μ (Iic (-t)) = (μ.map (fun x => -x)) (Iic (-t)) := by rw [hm]
      _ = μ ((fun x : ℝ => -x) ⁻¹' Iic (-t)) := Measure.map_apply (by fun_prop) measurableSet_Iic
      _ = μ (Ici t) := by congr 1; ext x; simp
  have : NullSingletonClass μ := nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hr := congrArg ENNReal.toReal he
  change μ.real (Iic (-t)) = μ.real (Ici t) at hr
  have hc := measureReal_compl (μ := μ) measurableSet_Iic (s := Iic t)
  rw [compl_Iic, probReal_univ] at hc
  change cdf μ (-t) = 1 - cdf μ t
  simp only [cdf_eq_real]
  rw [hr, measureReal_congr (Ioi_ae_eq_Ici (μ := μ) (a := t)).symm]
  exact hc

end WorstCaseVaR.EntropyProof

end

/- Complete checked body: QuantileRisk -/
section

namespace WorstCaseVaR.EntropyProof
open WorstCaseVaR.Entropy MeasureTheory ProbabilityTheory Set

theorem gaussianTail_le_iff {n : ℕ} (xhat w : Returns n)
    (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef) (hw : w ≠ 0)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (γ : ℝ) :
    gaussianTail xhat Γ w γ ≤ p ↔
      -normalQuantile p * Real.sqrt (quadForm Γ w) - inner ℝ xhat w ≤ γ := by
  have hs : 0 < Real.sqrt (quadForm Γ w) := Real.sqrt_pos.mpr (aux_gte_pos w Γ hΓ hw)
  rw [gaussianTail, ← stdNormalCDF_neg, cdf_le_iff_le_quantile hp hp1]
  rw [← neg_div, div_le_iff₀ hs, real_inner_comm w xhat]
  constructor <;> intro h <;> linarith

end WorstCaseVaR.EntropyProof

end

/- Complete checked body: EntropyVaRCore -/
section

namespace WorstCaseVaR.EntropyProof
open WorstCaseVaR.Entropy MeasureTheory ProbabilityTheory Set

theorem entropy_var_isLeast {n : ℕ} (xhat w : Returns n)
    (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef) (hw : w ≠ 0)
    (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    IsLeast (varFeasible (klBall xhat Γ d) w ε)
      (kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ xhat w) := by
  have hp := aux_kz_f_pos hε0 hε1 hd
  have hp1 : fEntropy ε d < 1 := (aux_kz_f_le hε0 hε1 hd).trans_lt hε1
  have he (γ : ℝ) : γ ∈ varFeasible (klBall xhat Γ d) w ε ↔
      kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ xhat w ≤ γ := by
    rw [varFeasible_iff_tail xhat w Γ hΓ hw ε d hε0 hε1 hd γ,
      gaussianTail_le_iff xhat w Γ hΓ hw hp hp1 γ]
    rfl
  exact ⟨(he _).mpr le_rfl, fun γ hγ => (he γ).mp hγ⟩

end WorstCaseVaR.EntropyProof

end

/- Complete checked body: EntropyVaRRoot -/
section

namespace WorstCaseVaR.Entropy

/-- Theorem 9, p. 553: when the distribution of returns is only known to satisfy the relative
entropy constraint `KL(P, P₀) ≤ d` with respect to the Gaussian `P₀ = 𝒩(x̂, Γ)`, `Γ ≻ 0`,
the entropy-constrained worst-case Value-at-Risk (4) of a portfolio `w ≠ 0` at level
`ε ∈ (0, 1)` is `V_𝒫(w) = κ(ε, d)√(wᵀΓw) - x̂ᵀw` (Eq. (44)): this value is the least `γ`
with `P{γ ≤ -wᵀx} ≤ ε` for every such `P`. -/
theorem entropy_constrained_var {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    IsLeast (varFeasible (klBall xhat Γ d) w ε)
      (kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ xhat w) := by
  exact WorstCaseVaR.EntropyProof.entropy_var_isLeast xhat w Γ hΓ hw ε d hε0 hε1 hd

end WorstCaseVaR.Entropy

end

open WorstCaseVaR.Entropy

theorem solution {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    IsLeast (varFeasible (klBall xhat Γ d) w ε)
      (kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ xhat w) := by
  exact WorstCaseVaR.Entropy.entropy_constrained_var xhat w Γ hΓ hw ε d hε0 hε1 hd

#print axioms WorstCaseVaR.Entropy.entropy_constrained_var
#print axioms solution
