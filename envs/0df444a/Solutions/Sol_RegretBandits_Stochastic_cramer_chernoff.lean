-- Prove2me | solution 1 for RegretBandits.Stochastic.cramer_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:41:40.437991+00:00
-- url     : https://prove2.me/submissions/eef864ce-09ed-46ed-b18b-a51f2160b126

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_model



namespace RegretBandits.Stochastic

open MeasureTheory ProbabilityTheory Real Finset

lemma cc_chernoff_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (Y k)) (hind : iIndepFun Y P)
    (hid : ∀ k, IdentDistrib (Y k) (Y 0) P P) (l c e : ℝ) (hl : 0 ≤ l)
    (hint : Integrable (fun ω => Real.exp (l * Y 0 ω)) P) (hc : mgf (Y 0) P l ≤ Real.exp c)
    (s : ℕ) (hs : 1 ≤ s) :
    P.real {ω | (s : ℝ) * e ≤ ∑ k ∈ range s, Y k ω} ≤
      Real.exp (-(l * ((s : ℝ) * e)) + s * c) := by
  have hint' : ∀ k ∈ range s, Integrable (fun ω => Real.exp (l * Y k ω)) P := by
    intro k _
    have := (hid k).comp (measurable_const_mul l).exp
    exact (this.integrable_iff).2 hint
  have hI := hind.integrable_exp_mul_sum (t := l) hm hint'
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ k ∈ range s, Y k) ((s : ℝ) * e) hl hI
  have h2 : mgf (∑ k ∈ range s, Y k) P l = mgf (Y 0) P l ^ s := by
    have := mgf_sum_of_identDistrib (μ := P) (X := Y) (s := range s) (j := 0) hm hind
      (fun i _ j _ => (hid i).trans (hid j).symm) (by simp; omega) l
    simpa using this
  rw [h2] at h1
  have h3 : mgf (Y 0) P l ^ s ≤ Real.exp c ^ s :=
    pow_le_pow_left₀ (mgf_nonneg) hc s
  have h4 : {ω | (s : ℝ) * e ≤ ∑ k ∈ range s, Y k ω} =
      {ω | (s : ℝ) * e ≤ (∑ k ∈ range s, Y k) ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [h4]
  calc _ ≤ _ := h1
    _ ≤ Real.exp (-l * ((s : ℝ) * e)) * Real.exp c ^ s := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

/-- For a stochastic bandit, functions of the arm-`i` rewards are independent. -/
lemma cc_indep_arm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ) (i : Fin K)
    (f : ℝ → ℝ) (hf : Measurable f) : iIndepFun (fun k => f ∘ X i k) P := by
  have h1 : iIndepFun (fun k : ℕ => X i k) P :=
    hX.indep.precomp (g := fun k : ℕ => (i, k)) (fun a b h => by simpa using h)
  exact h1.comp (fun _ => f) (fun _ => hf)

lemma cc_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (i : Fin K) (s : ℕ) (hs : 1 ≤ s) (ε : ℝ) (l : ℝ) (hl : 0 ≤ l) :
    P.real {ω | ε < μ i - sampleMean X i s ω} ≤ Real.exp (-((s : ℝ) * (l * ε - ψ l))) := by
  have hm : ∀ k, Measurable (fun ω => μ i - X i k ω) := fun k => measurable_const.sub (hX.measurable i k)
  have hind := cc_indep_arm P X μ hX i (fun x => μ i - x) (measurable_const.sub measurable_id)
  have hid : ∀ k, IdentDistrib (fun ω => μ i - X i k ω) (fun ω => μ i - X i 0 ω) P P :=
    fun k => (hX.identDistrib i k).comp (measurable_const.sub measurable_id)
  obtain ⟨_, _, hint, hlog⟩ := hψ.2 i l hl
  have hpos : 0 < ∫ ω, Real.exp (l * (μ i - X i 0 ω)) ∂P := by
    apply integral_exp_pos hint
  have hc : mgf (fun ω => μ i - X i 0 ω) P l ≤ Real.exp (ψ l) := by
    have := (Real.log_le_iff_le_exp hpos).1 hlog
    simpa [mgf] using this
  have key := cc_chernoff_sum P (fun k ω => μ i - X i k ω) hm hind hid l (ψ l) ε hl
    (by simpa using hint) hc s hs
  refine le_trans (measureReal_mono ?_) (le_trans key (le_of_eq ?_))
  · intro ω hω
    simp only [Set.mem_ofPred_eq, sampleMean] at hω ⊢
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (∑ k ∈ range s, X i k ω) / s < μ i - ε := by linarith
    rw [div_lt_iff₀ hs0] at this
    nlinarith
  · congr 1; ring


lemma cc_ereal_step (p : ENNReal) (s : ℕ) (hs : 1 ≤ s) (L : EReal) (hLbot : L ≠ ⊥)
    (H : ∀ x : ℝ, (x : EReal) < L → p ≤ ENNReal.ofReal (Real.exp (-((s : ℝ) * x)))) :
    p ≤ EReal.exp (-((s : ℝ) : EReal) * L) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  induction L using EReal.rec with
  | bot => exact absurd rfl hLbot
  | top =>
    have : (-((s : ℝ) : EReal)) * (⊤ : EReal) = ⊥ := by
      rw [EReal.mul_top_of_neg]
      exact EReal.coe_neg _ ▸ (by exact_mod_cast (neg_neg_of_pos hs0))
    rw [this]
    simp only [EReal.exp_bot, nonpos_iff_eq_zero]
    have hT : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-((s : ℝ) * (n : ℝ)))))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => -((s : ℝ) * (n : ℝ))) Filter.atTop Filter.atBot := by
        apply Filter.tendsto_neg_atTop_atBot.comp
        exact Filter.Tendsto.const_mul_atTop hs0 tendsto_natCast_atTop_atTop
      have h2 := (Real.tendsto_exp_atBot.comp h1)
      have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp h2
      simp only [ENNReal.ofReal_zero] at h3
      exact h3
    exact nonpos_iff_eq_zero.1 (ge_of_tendsto' hT (fun n => H n (by exact EReal.coe_lt_top _)))
  | coe c =>
    have : (-((s : ℝ) : EReal)) * (c : EReal) = ((-((s : ℝ) * c) : ℝ) : EReal) := by
      rw [← EReal.coe_neg, ← EReal.coe_mul]; congr 1; ring
    rw [this, EReal.exp_coe]
    have hT : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-((s : ℝ) * (c - 1 / ((n : ℝ) + 1))))))
        Filter.atTop (nhds (ENNReal.ofReal (Real.exp (-((s : ℝ) * c))))) := by
      have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Filter.Tendsto (fun n : ℕ => -((s : ℝ) * (c - 1 / ((n : ℝ) + 1)))) Filter.atTop
          (nhds (-((s : ℝ) * (c - 0)))) :=
        (continuous_neg.tendsto _).comp (((continuous_const.mul
          (continuous_const.sub continuous_id)).tendsto _).comp h1)
      have h3 := (ENNReal.continuous_ofReal.tendsto _).comp
        ((Real.continuous_exp.tendsto _).comp h2)
      simp only [sub_zero] at h3
      exact h3
    refine ge_of_tendsto' hT (fun n => H _ ?_)
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact_mod_cast (by linarith : c - 1 / ((n : ℝ) + 1) < c)

theorem cc_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l) (i : Fin K) (s : ℕ) (hs : 1 ≤ s) (ε : ℝ)
    (hε : 0 ≤ ε) :
    P {ω | ε < μ i - sampleMean X i s ω} ≤
      EReal.exp (-((s : ℝ) : EReal) * legendreFenchel ψ ε) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hbot : legendreFenchel ψ ε ≠ ⊥ := by
    intro h
    have : ((0 * ε - ψ 0 : ℝ) : EReal) ≤ legendreFenchel ψ ε := le_iSup (fun l : ℝ => ((l * ε - ψ l : ℝ) : EReal)) 0
    rw [h] at this
    exact absurd (le_bot_iff.1 this) (EReal.coe_ne_bot _)
  apply cc_ereal_step _ s hs _ hbot
  intro x hx
  have hx' : ∃ l : ℝ, x < l * ε - ψ l := by
    have := (lt_iSup_iff).1 hx
    obtain ⟨l, hl⟩ := this
    exact ⟨l, by exact_mod_cast hl⟩
  obtain ⟨l, hl⟩ := hx'
  have : ∃ l' : ℝ, 0 ≤ l' ∧ x ≤ l' * ε - ψ l' := by
    by_cases h0 : 0 ≤ l
    · exact ⟨l, h0, hl.le⟩
    · push_neg at h0
      refine ⟨0, le_rfl, ?_⟩
      have := hψneg l h0.le
      nlinarith
  obtain ⟨l', hl'0, hl'⟩ := this
  have h1 := cc_real P X μ hX ψ hψ i s hs ε l' hl'0
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  refine h1.trans (Real.exp_le_exp.2 ?_)
  nlinarith

end RegretBandits.Stochastic

open RegretBandits.Stochastic
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l) (i : Fin K) (s : ℕ) (hs : 1 ≤ s) (ε : ℝ)
    (hε : 0 ≤ ε) :
    P {ω | ε < μ i - sampleMean X i s ω} ≤
      EReal.exp (-((s : ℝ) : EReal) * legendreFenchel ψ ε) := by
  exact cc_core P X μ hX ψ hψ hψneg i s hs ε hε
