-- Prove2me | solution 1 for ProbEffIS.GE.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:05:28.629982+00:00
-- url     : https://prove2.me/submissions/6db5bd7c-f582-4ab4-a93e-e5b38fc89467

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs
import Theorems.Thm_ProbEffIS_GE_theorem_1
import Theorems.Thm_ProbEffIS_GE_theorem_2
import Theorems.Thm_ProbEffIS_GE_halfspace_bound
import Theorems.Thm_ProbEffIS_GE_p2_decay
import Theorems.Thm_ProbEffIS_GE_tilted_decay
import Theorems.Thm_ProbEffIS_GE_theorem_3

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE.T6

variable {d : ℕ}

/-- The density of the mixture with respect to the original law. -/
noncomputable def mixDens (ν : ℝ → Measure (Rd d)) (γ : ℝ) {r : ℕ} (S : Finset (Fin r))
    (α : Fin r → ℝ) (s : Fin r → Rd d) (x : Rd d) : ℝ :=
  ∑ i ∈ S, α i * (Real.exp (inner ℝ (s i) x) / ∫ y, Real.exp (inner ℝ (s i) y) ∂(ν γ))

lemma mixDens_continuous (ν : ℝ → Measure (Rd d)) (γ : ℝ) {r : ℕ} (S : Finset (Fin r))
    (α : Fin r → ℝ) (s : Fin r → Rd d) : Continuous (mixDens ν γ S α s) := by
  unfold mixDens
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  exact (Real.continuous_exp.comp (continuous_const.inner continuous_id)).div_const _

lemma mixDens_nonneg (ν : ℝ → Measure (Rd d)) (γ : ℝ) {r : ℕ} (S : Finset (Fin r))
    (α : Fin r → ℝ) (s : Fin r → Rd d) (hα : ∀ i ∈ S, 0 ≤ α i) (x : Rd d) :
    0 ≤ mixDens ν γ S α s x := by
  unfold mixDens
  refine Finset.sum_nonneg fun i hi => mul_nonneg (hα i hi) (div_nonneg (Real.exp_pos _).le ?_)
  exact integral_nonneg fun _ => (Real.exp_pos _).le

lemma mixDens_pos (ν : ℝ → Measure (Rd d)) (γ : ℝ) [IsProbabilityMeasure (ν γ)] {r : ℕ}
    (S : Finset (Fin r)) (hS : S.Nonempty)
    (α : Fin r → ℝ) (s : Fin r → Rd d) (hα : ∀ i ∈ S, 0 < α i)
    (hint : ∀ i ∈ S, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ)) (x : Rd d) :
    0 < mixDens ν γ S α s x := by
  unfold mixDens
  refine Finset.sum_pos (fun i hi => mul_pos (hα i hi) (div_pos (Real.exp_pos _) ?_)) hS
  exact integral_exp_pos (hint i hi)

lemma likelihoodRatio_eq (ν : ℝ → Measure (Rd d)) (γ : ℝ) {r : ℕ} (S : Finset (Fin r))
    (α : Fin r → ℝ) (s : Fin r → Rd d) (x : Rd d) :
    likelihoodRatio ν γ S α s x = (mixDens ν γ S α s x)⁻¹ := rfl

lemma mixtureIS_eq (ν : ℝ → Measure (Rd d)) (γ : ℝ) {r : ℕ} (S : Finset (Fin r))
    (α : Fin r → ℝ) (s : Fin r → Rd d) (hα : ∀ i ∈ S, 0 ≤ α i) :
    mixtureIS ν γ S α s =
      (ν γ).withDensity (fun x => ENNReal.ofReal (mixDens ν γ S α s x)) := by
  unfold mixtureIS mixDens
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, ih (fun i hi => hα i (Finset.mem_insert_of_mem hi))]
    have hmeas : Measurable fun x : Rd d => ENNReal.ofReal (α j *
        (Real.exp (inner ℝ (s j) x) / ∫ y, Real.exp (inner ℝ (s j) y) ∂(ν γ))) := by
      refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
      exact continuous_const.mul
        ((Real.continuous_exp.comp (continuous_const.inner continuous_id)).div_const _)
    have hZ : 0 ≤ ∫ y, Real.exp (inner ℝ (s j) y) ∂(ν γ) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have hαj : 0 ≤ α j := hα j (Finset.mem_insert_self _ _)
    have h1 : ENNReal.ofReal (α j) • (ν γ).tilted (fun x => inner ℝ (s j) x) =
        (ν γ).withDensity (fun x => ENNReal.ofReal (α j *
          (Real.exp (inner ℝ (s j) x) / ∫ y, Real.exp (inner ℝ (s j) y) ∂(ν γ)))) := by
      rw [Measure.tilted, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [ENNReal.ofReal_mul hαj]
    rw [h1, ← withDensity_add_left hmeas]
    congr 1
    funext x
    simp only [Pi.add_apply]
    rw [← ENNReal.ofReal_add (mul_nonneg hαj (div_nonneg (Real.exp_pos _).le hZ)),
      Finset.sum_insert hj]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hα i (Finset.mem_insert_of_mem hi))
      (div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le))


lemma mixtureIS_prob (ν : ℝ → Measure (Rd d)) (γ : ℝ) [IsProbabilityMeasure (ν γ)] {r : ℕ}
    (S : Finset (Fin r)) (α : Fin r → ℝ) (s : Fin r → Rd d) (hα : ∀ i ∈ S, 0 < α i)
    (hα1 : ∑ i ∈ S, α i = 1)
    (hint : ∀ i ∈ S, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ)) :
    IsProbabilityMeasure (mixtureIS ν γ S α s) := by
  constructor
  unfold mixtureIS
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have : ∀ i ∈ S, (ENNReal.ofReal (α i) • (ν γ).tilted (fun x => inner ℝ (s i) x)) Set.univ
      = ENNReal.ofReal (α i) := by
    intro i hi
    have := isProbabilityMeasure_tilted (μ := ν γ) (f := fun x => inner ℝ (s i) x) (hint i hi)
    simp
  rw [Finset.sum_congr rfl this, ← ENNReal.ofReal_sum_of_nonneg (fun i hi => (hα i hi).le), hα1]
  simp

lemma nu_eq_withDensity (ν : ℝ → Measure (Rd d)) (γ : ℝ) [IsProbabilityMeasure (ν γ)] {r : ℕ}
    (S : Finset (Fin r)) (hS : S.Nonempty) (α : Fin r → ℝ) (s : Fin r → Rd d)
    (hα : ∀ i ∈ S, 0 < α i)
    (hint : ∀ i ∈ S, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ)) :
    ν γ = (mixtureIS ν γ S α s).withDensity
      (fun x => ENNReal.ofReal (likelihoodRatio ν γ S α s x)) := by
  rw [mixtureIS_eq ν γ S α s (fun i hi => (hα i hi).le), ← withDensity_mul]
  · conv_lhs => rw [← withDensity_one (μ := ν γ)]
    congr 1
    funext x
    simp only [Pi.mul_apply, Pi.one_apply, likelihoodRatio_eq]
    rw [← ENNReal.ofReal_mul (mixDens_nonneg ν γ S α s (fun i hi => (hα i hi).le) x),
      mul_inv_cancel₀ (mixDens_pos ν γ S hS α s hα hint x).ne']
    simp
  · exact ENNReal.measurable_ofReal.comp (mixDens_continuous ν γ S α s).measurable
  · simp only [likelihoodRatio_eq]
    exact ENNReal.measurable_ofReal.comp (mixDens_continuous ν γ S α s).measurable.inv

lemma rnDeriv_mix (ν : ℝ → Measure (Rd d)) (γ : ℝ) [IsProbabilityMeasure (ν γ)] {r : ℕ}
    (S : Finset (Fin r)) (hS : S.Nonempty) (α : Fin r → ℝ) (s : Fin r → Rd d)
    (hα : ∀ i ∈ S, 0 < α i) (hα1 : ∑ i ∈ S, α i = 1)
    (hint : ∀ i ∈ S, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ)) :
    (ν γ).rnDeriv (mixtureIS ν γ S α s) =ᵐ[mixtureIS ν γ S α s]
      fun x => ENNReal.ofReal (likelihoodRatio ν γ S α s x) := by
  have := mixtureIS_prob ν γ S α s hα hα1 hint
  have h := nu_eq_withDensity ν γ S hS α s hα hint
  have hm : Measurable fun x => ENNReal.ofReal (likelihoodRatio ν γ S α s x) := by
    simp only [likelihoodRatio_eq]
    exact ENNReal.measurable_ofReal.comp (mixDens_continuous ν γ S α s).measurable.inv
  have := Measure.rnDeriv_withDensity (mixtureIS ν γ S α s) hm
  rw [← h] at this
  exact this

lemma lrOutput_mix (ν : ℝ → Measure (Rd d)) (γ : ℝ) [IsProbabilityMeasure (ν γ)] {r : ℕ}
    (S : Finset (Fin r)) (hS : S.Nonempty) (α : Fin r → ℝ) (s : Fin r → Rd d)
    (hα : ∀ i ∈ S, 0 < α i) (hα1 : ∑ i ∈ S, α i = 1)
    (hint : ∀ i ∈ S, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ)) (B : Set (Rd d)) :
    lrOutput (ν γ) (mixtureIS ν γ S α s) B =ᵐ[mixtureIS ν γ S α s]
      B.indicator (likelihoodRatio ν γ S α s) := by
  filter_upwards [rnDeriv_mix ν γ S hS α s hα hα1 hint] with x hx
  unfold lrOutput
  by_cases hB : x ∈ B
  · simp only [Set.indicator_of_mem hB, hx]
    rw [ENNReal.toReal_ofReal]
    rw [likelihoodRatio_eq]
    exact inv_nonneg.2 (mixDens_nonneg ν γ S α s (fun i hi => (hα i hi).le) x)
  · simp [Set.indicator_of_notMem hB]

lemma nu_ac_mix (ν : ℝ → Measure (Rd d)) (γ : ℝ) [IsProbabilityMeasure (ν γ)] {r : ℕ}
    (S : Finset (Fin r)) (hS : S.Nonempty) (α : Fin r → ℝ) (s : Fin r → Rd d)
    (hα : ∀ i ∈ S, 0 < α i)
    (hint : ∀ i ∈ S, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ)) :
    ν γ ≪ mixtureIS ν γ S α s := by
  rw [nu_eq_withDensity ν γ S hS α s hα hint]
  exact withDensity_absolutelyContinuous _ _


lemma minRelDisc_congr {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (n : ℕ) (Z Z' : Ω → ℝ) (hZ : Z =ᵐ[Q] Z') (p ε : ℝ) :
    minRelDisc Q n Z p ε = minRelDisc Q n Z' p ε := by
  unfold minRelDisc
  congr 1
  ext δ
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Fin n => Q), ∀ i, Z (ω i) = Z' (ω i) := by
    refine ae_all_iff.2 fun i => ?_
    exact (measurePreserving_eval (fun _ : Fin n => Q) i).quasiMeasurePreserving.ae_eq_comp hZ
  have : {ω : Fin n → Ω | δ * p < |sampleMean n Z ω - p|} =ᵐ[Measure.pi fun _ : Fin n => Q]
      {ω | δ * p < |sampleMean n Z' ω - p|} := by
    filter_upwards [hall] with ω hω
    change (δ * p < |sampleMean n Z ω - p|) = (δ * p < |sampleMean n Z' ω - p|)
    simp only [sampleMean, hω]
  rw [measure_congr this]

lemma spe_congr {Ω : Type*} [MeasurableSpace Ω] (Q : ℝ → Measure Ω)
    (hQ : ∀ᶠ γ in atTop, IsProbabilityMeasure (Q γ)) (Z Z' : ℝ → Ω → ℝ) (p p' : ℝ → ℝ)
    (hp : ∀ᶠ γ in atTop, p γ = p' γ) (hZ : ∀ᶠ γ in atTop, Z γ =ᵐ[Q γ] Z' γ)
    (h : StronglyProbEfficient Q Z p) : StronglyProbEfficient Q Z' p' := by
  obtain ⟨h0, n, hn, hsub, hdisc⟩ := h
  refine ⟨h0.congr' hp, n, hn, ?_, fun ε hε => ?_⟩
  · unfold IsSubexpIn at hsub ⊢
    refine hsub.congr' ?_
    filter_upwards [hp] with γ h
    rw [h]
  · refine (hdisc ε hε).congr' ?_
    filter_upwards [hp, hZ, hQ] with γ h1 h2 h3
    rw [h1, minRelDisc_congr (Q γ) (n γ) (Z γ) (Z' γ) h2]


lemma lrOutput_integral {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (A : Set Ω) (hA : MeasurableSet A) (hac : P.restrict A ≪ Q) :
    ∫ ω, lrOutput P Q A ω ∂Q = (P A).toReal := by
  have h1 : lrOutput P Q A =ᵐ[Q] fun ω => ((P.restrict A).rnDeriv Q ω).toReal := by
    filter_upwards [Measure.rnDeriv_restrict P Q hA] with ω hω
    rw [hω, lrOutput]
    by_cases h : ω ∈ A <;> simp [h]
  rw [integral_congr_ae h1, Measure.integral_toReal_rnDeriv hac]
  simp [measureReal_def]

lemma tilted_ne_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (A : Set Ω) : P.tilted f A ≠ ⊤ := by
  by_cases hf : Integrable (fun x => Real.exp (f x)) P
  · have := isProbabilityMeasure_tilted hf
    exact measure_ne_top _ _
  · rw [tilted_of_not_integrable hf]; simp

/-- Converting an `EReal` exponential rate into real form. -/
lemma rate_real (m : ℝ → ENNReal) (L : ℝ)
    (h : Tendsto (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) * ENNReal.log (m γ)) atTop (𝓝 (L : EReal))) :
    (∀ᶠ γ in atTop, 0 < m γ ∧ m γ < ⊤) ∧
    Tendsto (fun γ => γ⁻¹ * Real.log (m γ).toReal) atTop (𝓝 L) := by
  have hbot : ∀ᶠ γ in atTop, ⊥ < ((γ⁻¹ : ℝ) : EReal) * ENNReal.log (m γ) :=
    h.eventually (lt_mem_nhds (EReal.bot_lt_coe L))
  have htop : ∀ᶠ γ in atTop, ((γ⁻¹ : ℝ) : EReal) * ENNReal.log (m γ) < ⊤ :=
    h.eventually (gt_mem_nhds (EReal.coe_lt_top L))
  have hpos : ∀ᶠ γ in atTop, (0 : ℝ) < γ := eventually_gt_atTop 0
  have hm : ∀ᶠ γ in atTop, 0 < m γ ∧ m γ < ⊤ := by
    filter_upwards [hbot, htop, hpos] with γ hb ht hγ
    have hγ' : (0 : ℝ) < γ⁻¹ := inv_pos.2 hγ
    constructor
    · rcases eq_or_ne (m γ) 0 with h0 | h0
      · rw [h0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hγ'] at hb
        exact absurd hb (lt_irrefl _)
      · exact pos_iff_ne_zero.2 h0
    · rcases eq_or_ne (m γ) ⊤ with h0 | h0
      · rw [h0, ENNReal.log_top, EReal.coe_mul_top_of_pos hγ'] at ht
        exact absurd ht (lt_irrefl _)
      · exact lt_top_iff_ne_top.2 h0
  refine ⟨hm, ?_⟩
  rw [← EReal.tendsto_coe]
  refine h.congr' ?_
  filter_upwards [hm] with γ ⟨h0, ht⟩
  have hr : 0 < (m γ).toReal := ENNReal.toReal_pos h0.ne' ht.ne
  conv_lhs => rw [← ENNReal.ofReal_toReal ht.ne, ENNReal.log_ofReal_of_pos hr]
  rw [EReal.coe_mul]

/-- An exponential upper bound from an `EReal` limsup bound. -/
lemma rate_upper (m : ℝ → ENNReal) (hm : ∀ γ, m γ ≠ ⊤) (c : ℝ)
    (h : limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) * ENNReal.log (m γ)) atTop < (c : EReal)) :
    ∀ᶠ γ in atTop, (m γ).toReal ≤ Real.exp (γ * c) := by
  filter_upwards [eventually_lt_of_limsup_lt h, eventually_gt_atTop (0 : ℝ)] with γ hγ hγ0
  rcases eq_or_ne (m γ) 0 with h0 | h0
  · rw [h0]; simp; exact (Real.exp_pos _).le
  have hr : 0 < (m γ).toReal := ENNReal.toReal_pos h0 (hm γ)
  rw [← ENNReal.ofReal_toReal (hm γ), ENNReal.log_ofReal_of_pos hr, ← EReal.coe_mul,
    EReal.coe_lt_coe_iff] at hγ
  have : Real.log (m γ).toReal < γ * c := by
    rw [inv_mul_lt_iff₀ hγ0] at hγ; exact hγ
  exact (Real.log_lt_iff_lt_exp hr |>.1 this).le

end ProbEffIS.GE.T6

open ProbEffIS.GE ProbEffIS.GE.T6 in
theorem solution {d r : ℕ} (ν : ℝ → Measure (Rd d))
    [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (h2 : Assumption2 μ R)
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s)
    (S : Finset (Fin r)) (hS : IsMostSignificant μ a S)
    (α : Fin r → ℝ) (hα : ∀ i ∈ S, 0 < α i)
    (hα1 : ∑ i ∈ S, α i = 1) :
    StronglyProbEfficient
      (fun γ => mixtureIS ν γ S α s)
      (fun γ => isOutput ν γ R S α s)
      (fun γ => rareProb ν γ R) := by
  have hSmost := hS
  obtain ⟨hSne, hSeq, hSlt⟩ := hS
  ------------------------------------------------------------------
  -- Step 0: the rates of the most significant points
  obtain ⟨i₀, hi₀R, hi₀min⟩ := theorem_2 ν μ h1 R h2 a s hA
  have hrateS : ∀ i ∈ S, rate μ (a i) = rateOn μ R := by
    intro i hi
    by_cases h0 : i₀ ∈ S
    · rw [hi₀R]; exact hSeq i hi i₀ h0
    · exact absurd (hi₀min i) (not_le.2 (hSlt i hi i₀ h0))
  have hhalf : ∀ i, rate μ (a i) = ((inner ℝ (s i) (a i) : ℝ) : EReal) - μ (s i) := fun i =>
    (halfspace_bound ν μ h1 (s i) (a i) (hA.tilt_mem i) (hA.grad_eq i)).1
  have hrate_top : ∀ i, rate μ (a i) < ⊤ := fun i =>
    (interior_subset (hA.mem_interior_dom_rate i) : a i ∈ dom (rate μ))
  obtain ⟨i₁, hi₁⟩ := hSne
  have hRtop : rateOn μ R ≠ ⊤ := by rw [← hrateS i₁ hi₁]; exact (hrate_top i₁).ne
  have hRpos : 0 < rateOn μ R := h2.pos
  set I : ℝ := (rateOn μ R).toReal with hI_def
  have hI : rateOn μ R = (I : EReal) := (EReal.coe_toReal hRtop (ne_bot_of_gt hRpos)).symm
  have hIpos : 0 < I := by
    have := hRpos; rw [hI] at this; exact_mod_cast this
  have hμtop : ∀ i, μ (s i) ≠ ⊤ := fun i => (interior_subset (hA.tilt_mem i) : s i ∈ dom μ).ne
  have hμbot : ∀ i ∈ S, μ (s i) ≠ ⊥ := by
    intro i hi h
    have := hrate_top i
    rw [hhalf i, h, EReal.coe_sub_bot] at this
    exact lt_irrefl _ this
  set M : Fin r → ℝ := fun i => (μ (s i)).toReal with hM_def
  have hM : ∀ i ∈ S, μ (s i) = (M i : EReal) := fun i hi =>
    (EReal.coe_toReal (hμtop i) (hμbot i hi)).symm
  have hIM : ∀ i ∈ S, I = inner ℝ (s i) (a i) - M i := by
    intro i hi
    have h := hrateS i hi
    rw [hhalf i, hM i hi, hI, ← EReal.coe_sub, EReal.coe_eq_coe_iff] at h
    exact h.symm
  ------------------------------------------------------------------
  -- Step 1: the scaled log-MGF at the selected tilts
  set Zi : Fin r → ℝ → ℝ := fun i γ => ∫ y, Real.exp (inner ℝ (s i) y) ∂(ν γ) with hZi_def
  have hstep1 : ∀ i ∈ S, (∀ᶠ γ in atTop, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ)) ∧
      Tendsto (fun γ => γ⁻¹ * Real.log (Zi i γ)) atTop (𝓝 (M i)) := by
    intro i hi
    have ht := h1.tendsto (s i)
    rw [hM i hi] at ht
    obtain ⟨hJ, hlim⟩ := rate_real
      (fun γ => ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ (s i) y)) ∂(ν γ)) (M i) ht
    have hint : ∀ᶠ γ in atTop, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ) := by
      filter_upwards [hJ] with γ ⟨_, hlt⟩
      refine ⟨(Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      simpa [Real.enorm_eq_ofReal (Real.exp_pos _).le] using hlt
    refine ⟨hint, hlim.congr' ?_⟩
    filter_upwards [hint] with γ hγ
    simp only [hZi_def]
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => (Real.exp_pos _).le)
      hγ.1]
  ------------------------------------------------------------------
  -- Step 2: the rare-event probability
  set p : ℝ → ℝ := fun γ => rareProb ν γ R with hp_def
  have hstep2 : (∀ᶠ γ in atTop, 0 < p γ) ∧
      Tendsto (fun γ => γ⁻¹ * Real.log (p γ)) atTop (𝓝 (-I)) := by
    have ht := (theorem_1 ν (Eventually.of_forall inferInstance) μ h1 R h2.measurable).2.2 h2 r a s hA
    rw [hI, ← EReal.coe_neg] at ht
    obtain ⟨hm, hlim⟩ := rate_real (fun γ => ν γ {x | γ⁻¹ • x ∈ R}) (-I) ht
    refine ⟨?_, hlim⟩
    filter_upwards [hm] with γ ⟨h0, ht⟩
    exact ENNReal.toReal_pos h0.ne' ht.ne
  ------------------------------------------------------------------
  -- Step 3: the omitted region
  set p₂ : ℝ → ℝ := fun γ => rareProb ν γ (splitOut R S a s) with hp₂_def
  have hstep3 : Tendsto (fun γ => p₂ γ / p γ) atTop (𝓝 0) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ i ∈ S, ∀ᶠ γ in atTop,
        ((ν γ).tilted (fun x => inner ℝ (s i) x) {x | γ⁻¹ • x ∈ splitOut R S a s}).toReal
          ≤ Real.exp (γ * (-c)) := by
    by_cases hSu : S = Finset.univ
    · have hempty : splitOut R S a s = ∅ := by
        subst hSu
        ext x
        simp only [splitOut, splitIn, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hx h
        exact h hx (by have := hA.cover hx; simpa using this)
      refine ⟨?_, 1, one_pos, fun i _ => Eventually.of_forall fun γ => ?_⟩
      · simp [p₂, hempty, rareProb]
      · simp only [hempty, Set.mem_empty_iff_false, Set.ofPred_false, measure_empty,
          ENNReal.toReal_zero]
        positivity
    · have hpd := p2_decay ν μ h1 R h2 a s hA S hSmost hSu
      have htd := tilted_decay ν μ h1 R h2 a s hA S hSmost hSu
      refine ⟨hpd.2.2, ?_⟩
      have hc : 0 < (⨅ j ∈ (Finset.univ \ S), rate μ (a j)) - rateOn μ R := by
        have := ((htd i₁ hi₁).2); rwa [hrateS i₁ hi₁] at this
      obtain ⟨c', hc'0, hc'⟩ := exists_between hc
      have hc'top : c' ≠ ⊤ := (lt_of_lt_of_le hc' le_top).ne
      refine ⟨c'.toReal, EReal.toReal_pos hc'0 hc'top, fun i hi => ?_⟩
      have h := (htd i hi).1
      rw [hrateS i hi] at h
      apply rate_upper _ (fun γ => tilted_ne_top _ _ _) _
      refine lt_of_le_of_lt h ?_
      rw [EReal.coe_neg, EReal.coe_toReal hc'top (ne_bot_of_gt hc'0)]
      exact EReal.neg_lt_neg_iff.2 hc'
  obtain ⟨hP2, c, hc, hT2⟩ := hstep3
  ------------------------------------------------------------------
  -- Step 4: a threshold beyond which all selected tilts are integrable
  have hev_int : ∀ᶠ γ in atTop, 1 ≤ γ ∧
      ∀ i ∈ S, Integrable (fun y => Real.exp (inner ℝ (s i) y)) (ν γ) := by
    filter_upwards [eventually_ge_atTop (1:ℝ),
      (eventually_all_finset S).2 (fun i hi => (hstep1 i hi).1)] with γ h1' h2'
    exact ⟨h1', h2'⟩
  obtain ⟨γ₀, hγ₀⟩ := eventually_atTop.1 hev_int
  have hSne' : S.Nonempty := ⟨i₁, hi₁⟩
  set Q : ℝ → Measure (Rd d) := fun γ => mixtureIS ν γ S α s with hQ_def
  have hQprob : ∀ γ, γ₀ ≤ γ → IsProbabilityMeasure (Q γ) := fun γ hγ =>
    mixtureIS_prob ν γ S α s hα hα1 (hγ₀ γ hγ).2
  have hQev : ∀ᶠ γ in atTop, IsProbabilityMeasure (Q γ) := by
    filter_upwards [eventually_ge_atTop γ₀] with γ hγ using hQprob γ hγ
  -- measurability of the pieces
  have hhs : ∀ i, MeasurableSet (halfspace (s i) (a i)) := fun i =>
    (isClosed_le continuous_const
      (continuous_const.inner (continuous_id.sub continuous_const))).measurableSet
  have hIn_meas : MeasurableSet (splitIn R S a s) :=
    h2.measurable.inter (Finset.measurableSet_biUnion S fun i _ => hhs i)
  have hOut_meas : MeasurableSet (splitOut R S a s) := h2.measurable.diff hIn_meas
  have hpre : ∀ (γ : ℝ) (B : Set (Rd d)), MeasurableSet B → MeasurableSet {x : Rd d | γ⁻¹ • x ∈ B} :=
    fun γ B hB => (continuous_const_smul γ⁻¹).measurable hB
  set E₁ : ℝ → Set (Rd d) := fun γ => {x | γ⁻¹ • x ∈ splitIn R S a s} with hE₁_def
  set E₂ : ℝ → Set (Rd d) := fun γ => {x | γ⁻¹ • x ∈ splitOut R S a s} with hE₂_def
  have hE₁m : ∀ γ, MeasurableSet (E₁ γ) := fun γ => hpre γ _ hIn_meas
  have hE₂m : ∀ γ, MeasurableSet (E₂ γ) := fun γ => hpre γ _ hOut_meas
  have hE_disj : ∀ γ, Disjoint (E₁ γ) (E₂ γ) := fun γ => by
    refine Set.disjoint_left.2 fun x h1 h2 => ?_
    exact h2.2 h1
  have hE_union : ∀ γ, E₁ γ ∪ E₂ γ = {x | γ⁻¹ • x ∈ R} := fun γ => by
    ext x
    simp only [hE₁_def, hE₂_def, Set.mem_union, Set.mem_ofPred_eq, splitOut]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      by_cases h' : γ⁻¹ • x ∈ splitIn R S a s
      · exact Or.inl h'
      · exact Or.inr ⟨h, h'⟩
  set p₁ : ℝ → ℝ := fun γ => rareProb ν γ (splitIn R S a s) with hp₁_def
  have hpsum : ∀ γ, p γ = p₁ γ + p₂ γ := fun γ => by
    simp only [hp_def, hp₁_def, hp₂_def, rareProb]
    rw [← hE_union γ, measure_union (hE_disj γ) (hE₂m γ),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hp₂0 : ∀ γ, 0 ≤ p₂ γ := fun γ => ENNReal.toReal_nonneg
  have hp₁0 : ∀ γ, 0 ≤ p₁ γ := fun γ => ENNReal.toReal_nonneg
  set A₁ : ℝ → Set (Rd d) := fun γ => if γ₀ ≤ γ then E₁ γ else ∅ with hA₁_def
  set A₂ : ℝ → Set (Rd d) := fun γ => if γ₀ ≤ γ then E₂ γ else ∅ with hA₂_def
  have hA₁e : ∀ γ, γ₀ ≤ γ → A₁ γ = E₁ γ := fun γ h => by simp [hA₁_def, h]
  have hA₂e : ∀ γ, γ₀ ≤ γ → A₂ γ = E₂ γ := fun γ h => by simp [hA₂_def, h]
  have hA₁m : ∀ γ, MeasurableSet (A₁ γ) := fun γ => by
    by_cases h : γ₀ ≤ γ
    · rw [hA₁e γ h]; exact hE₁m γ
    · simp [hA₁_def, h]
  have hA₂m : ∀ γ, MeasurableSet (A₂ γ) := fun γ => by
    by_cases h : γ₀ ≤ γ
    · rw [hA₂e γ h]; exact hE₂m γ
    · simp [hA₂_def, h]
  have hAdisj : ∀ γ, Disjoint (A₁ γ) (A₂ γ) := fun γ => by
    by_cases h : γ₀ ≤ γ
    · rw [hA₁e γ h, hA₂e γ h]; exact hE_disj γ
    · simp [hA₁_def, h]
  have hac : ∀ γ, (ν γ).restrict (A₁ γ ∪ A₂ γ) ≪ Q γ := fun γ => by
    by_cases h : γ₀ ≤ γ
    · exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
        (nu_ac_mix ν γ S hSne' α s hα (hγ₀ γ h).2)
    · simp [hA₁_def, hA₂_def, h]
  ------------------------------------------------------------------
  -- Step 5: exponential estimates
  obtain ⟨hppos, hℓ⟩ := hstep2
  have hp_bd : ∀ η > 0, ∀ᶠ γ in atTop,
      Real.exp (γ * (-I - η)) ≤ p γ ∧ p γ ≤ Real.exp (γ * (-I + η)) := by
    intro η hη
    have h1' : ∀ᶠ γ in atTop, -I - η < γ⁻¹ * Real.log (p γ) :=
      hℓ.eventually (lt_mem_nhds (by linarith))
    have h2' : ∀ᶠ γ in atTop, γ⁻¹ * Real.log (p γ) < -I + η :=
      hℓ.eventually (gt_mem_nhds (by linarith))
    filter_upwards [h1', h2', hppos, eventually_gt_atTop (0:ℝ)] with γ ha hb hpγ hγ
    have hlog : Real.log (p γ) = γ * (γ⁻¹ * Real.log (p γ)) := by field_simp
    constructor
    · rw [← Real.exp_log hpγ, hlog]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ha.le hγ.le)
    · rw [← Real.exp_log hpγ, hlog]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hb.le hγ.le)
  have hp1half : ∀ᶠ γ in atTop, p γ / 2 ≤ p₁ γ := by
    have := hP2.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
    filter_upwards [this, hppos] with γ h hpγ
    rw [div_lt_iff₀ hpγ] at h
    linarith [hpsum γ]
  set B : ℝ → ℝ := fun γ => ∑ i ∈ S, Zi i γ * Real.exp (-(γ * inner ℝ (s i) (a i))) / α i
    with hB_def
  have hB_bd : ∀ η > 0, ∀ᶠ γ in atTop, B γ ≤ Real.exp (γ * (-I + η)) := by
    intro η hη
    have hterm : ∀ i ∈ S, ∀ᶠ γ in atTop, Zi i γ * Real.exp (-(γ * inner ℝ (s i) (a i))) / α i
        ≤ Real.exp (γ * (-I + η / 2)) / α i := by
      intro i hi
      have h' := (hstep1 i hi).2.eventually (gt_mem_nhds (show M i < M i + η / 2 by linarith))
      filter_upwards [h', (hstep1 i hi).1, eventually_gt_atTop (0:ℝ)] with γ hγ hint hγ0
      have hZpos : 0 < Zi i γ := integral_exp_pos hint
      have hZle : Zi i γ ≤ Real.exp (γ * (M i + η / 2)) := by
        have hl : Real.log (Zi i γ) < γ * (M i + η / 2) := by
          rw [inv_mul_lt_iff₀ hγ0] at hγ; exact hγ
        exact (Real.log_lt_iff_lt_exp hZpos |>.1 hl).le
      apply div_le_div_of_nonneg_right _ (hα i hi).le
      calc Zi i γ * Real.exp (-(γ * inner ℝ (s i) (a i)))
          ≤ Real.exp (γ * (M i + η / 2)) * Real.exp (-(γ * inner ℝ (s i) (a i))) :=
            mul_le_mul_of_nonneg_right hZle (Real.exp_pos _).le
        _ = Real.exp (γ * (-I + η / 2)) := by
            rw [← Real.exp_add]; congr 1; rw [hIM i hi]; ring
    have hC : ∀ᶠ γ in atTop, (∑ i ∈ S, (α i)⁻¹) ≤ Real.exp (γ * (η / 2)) :=
      (Real.tendsto_exp_atTop.comp (Tendsto.atTop_mul_const (by linarith) tendsto_id)).eventually_ge_atTop _
    filter_upwards [(eventually_all_finset S).2 hterm, hC] with γ hγ hCγ
    calc B γ ≤ ∑ i ∈ S, Real.exp (γ * (-I + η / 2)) / α i := Finset.sum_le_sum hγ
      _ = (∑ i ∈ S, (α i)⁻¹) * Real.exp (γ * (-I + η / 2)) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ Real.exp (γ * (η / 2)) * Real.exp (γ * (-I + η / 2)) :=
          mul_le_mul_of_nonneg_right hCγ (Real.exp_pos _).le
      _ = Real.exp (γ * (-I + η)) := by rw [← Real.exp_add]; ring_nf
  -- the likelihood ratio is bounded on the selected region
  have hLR : ∀ γ, γ₀ ≤ γ → ∀ x ∈ E₁ γ, likelihoodRatio ν γ S α s x ≤ B γ := by
    intro γ hγ x hx
    obtain ⟨hγ1, hint⟩ := hγ₀ γ hγ
    have hγ0 : 0 < γ := by linarith
    obtain ⟨-, hxU⟩ := hx
    simp only [Set.mem_iUnion] at hxU
    obtain ⟨i, hi, hxi⟩ := hxU
    have hin : γ * inner ℝ (s i) (a i) ≤ inner ℝ (s i) x := by
      have h0 : 0 ≤ inner ℝ (s i) (γ⁻¹ • x - a i) := hxi
      rw [inner_sub_right, inner_smul_right] at h0
      have := mul_le_mul_of_nonneg_left
        (show inner ℝ (s i) (a i) ≤ γ⁻¹ * inner ℝ (s i) x by linarith) hγ0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hγ0.ne', one_mul] at this
    have hZpos : ∀ j ∈ S, 0 < Zi j γ := fun j hj => integral_exp_pos (hint j hj)
    have hmix : mixDens ν γ S α s x =
        ∑ j ∈ S, α j * (Real.exp (inner ℝ (s j) x) / Zi j γ) := rfl
    have hterm : α i * (Real.exp (γ * inner ℝ (s i) (a i)) / Zi i γ) ≤ mixDens ν γ S α s x := by
      have h1' : α i * (Real.exp (γ * inner ℝ (s i) (a i)) / Zi i γ) ≤
          α i * (Real.exp (inner ℝ (s i) x) / Zi i γ) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (Real.exp_le_exp.2 hin)
          (hZpos i hi).le) (hα i hi).le
      rw [hmix]
      exact h1'.trans (Finset.single_le_sum
        (f := fun j => α j * (Real.exp (inner ℝ (s j) x) / Zi j γ))
        (fun j hj => mul_nonneg (hα j hj).le (div_nonneg (Real.exp_pos _).le (hZpos j hj).le)) hi)
    have htpos : 0 < α i * (Real.exp (γ * inner ℝ (s i) (a i)) / Zi i γ) :=
      mul_pos (hα i hi) (div_pos (Real.exp_pos _) (hZpos i hi))
    rw [likelihoodRatio_eq]
    calc (mixDens ν γ S α s x)⁻¹ ≤ (α i * (Real.exp (γ * inner ℝ (s i) (a i)) / Zi i γ))⁻¹ :=
          inv_anti₀ htpos hterm
      _ = Zi i γ * Real.exp (-(γ * inner ℝ (s i) (a i))) / α i := by
          rw [Real.exp_neg]
          have := (hα i hi).ne'
          have := (hZpos i hi).ne'
          field_simp
      _ ≤ B γ := Finset.single_le_sum
          (f := fun j => Zi j γ * Real.exp (-(γ * inner ℝ (s j) (a j))) / α j)
          (fun j hj => div_nonneg (mul_nonneg (hZpos j hj).le (Real.exp_pos _).le) (hα j hj).le) hi
  have hB0all : ∀ γ, 0 ≤ B γ := fun γ =>
    Finset.sum_nonneg fun j hj => div_nonneg (mul_nonneg
      (integral_nonneg fun _ => (Real.exp_pos _).le) (Real.exp_pos _).le) (hα j hj).le
  ------------------------------------------------------------------
  -- Step 6: the restricted estimator Z₁
  have hZ1 : ∀ γ, γ₀ ≤ γ →
      MemLp (eventOutput ν Q A₁ γ) 2 (Q γ) ∧
      variance (eventOutput ν Q A₁ γ) (Q γ) ≤ B γ * p₁ γ := by
    intro γ hγ
    have := hQprob γ hγ
    obtain ⟨hγ1, hint⟩ := hγ₀ γ hγ
    have hae : eventOutput ν Q A₁ γ =ᵐ[Q γ] (E₁ γ).indicator (likelihoodRatio ν γ S α s) := by
      have := lrOutput_mix ν γ S hSne' α s hα hα1 hint (E₁ γ)
      simp only [eventOutput, hA₁e γ hγ]
      exact this
    have hbd : ∀ᵐ x ∂(Q γ), 0 ≤ eventOutput ν Q A₁ γ x ∧ eventOutput ν Q A₁ γ x ≤ B γ := by
      filter_upwards [hae] with x hx
      rw [hx]
      by_cases hxE : x ∈ E₁ γ
      · rw [Set.indicator_of_mem hxE]
        refine ⟨?_, hLR γ hγ x hxE⟩
        rw [likelihoodRatio_eq]
        exact inv_nonneg.2 (mixDens_nonneg ν γ S α s (fun i hi => (hα i hi).le) x)
      · rw [Set.indicator_of_notMem hxE]
        exact ⟨le_rfl, hB0all γ⟩
    have hmeas : Measurable (eventOutput ν Q A₁ γ) :=
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal).indicator (hA₁m γ)
    have hL2 : MemLp (eventOutput ν Q A₁ γ) 2 (Q γ) := by
      refine MemLp.of_bound hmeas.aestronglyMeasurable (B γ) ?_
      filter_upwards [hbd] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2
    refine ⟨hL2, ?_⟩
    have hac₁ : (ν γ).restrict (A₁ γ) ≪ Q γ :=
      (Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono Set.subset_union_left le_rfl)).trans (hac γ)
    have hmean : ∫ x, eventOutput ν Q A₁ γ x ∂(Q γ) = p₁ γ := by
      have := lrOutput_integral (ν γ) (Q γ) (A₁ γ) (hA₁m γ) hac₁
      simp only [eventOutput]; rw [this, hA₁e γ hγ]; rfl
    calc variance (eventOutput ν Q A₁ γ) (Q γ) ≤ (Q γ)[eventOutput ν Q A₁ γ ^ 2] :=
          variance_le_expectation_sq hL2.1
      _ ≤ ∫ x, B γ * eventOutput ν Q A₁ γ x ∂(Q γ) := by
          apply integral_mono_ae hL2.integrable_sq ((hL2.integrable one_le_two).const_mul _)
          filter_upwards [hbd] with x hx
          show eventOutput ν Q A₁ γ x ^ 2 ≤ B γ * eventOutput ν Q A₁ γ x
          nlinarith [hx.1, hx.2]
      _ = B γ * p₁ γ := by rw [integral_const_mul, hmean]
  ------------------------------------------------------------------
  -- Step 7: the sample sizes
  set K : ℝ → ℝ := fun γ => B γ * p γ / p₁ γ ^ 2 with hK_def
  set n : ℝ → ℕ := fun γ => ⌈γ * max 1 (K γ)⌉₊ + 1 with hn_def
  have hn1 : ∀ γ, 1 ≤ n γ := fun γ => by simp [hn_def]
  have hnge : ∀ γ, γ * max 1 (K γ) ≤ (n γ : ℝ) := fun γ => by
    simp only [hn_def]; push_cast; linarith [Nat.le_ceil (γ * max 1 (K γ))]
  have hnle : ∀ᶠ γ in atTop, (n γ : ℝ) ≤ 3 * (γ * max 1 (K γ)) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with γ hγ
    have h1' : 1 ≤ γ * max 1 (K γ) := by nlinarith [le_max_left 1 (K γ)]
    simp only [hn_def]; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ γ * max 1 (K γ) by linarith)
    linarith
  have hK_bd : ∀ η > 0, ∀ᶠ γ in atTop, max 1 (K γ) ≤ 4 * Real.exp (γ * (2 * η)) := by
    intro η hη
    filter_upwards [hB_bd η hη, hp_bd η hη, hp1half, hppos, eventually_gt_atTop (0:ℝ)]
      with γ hB hp hp1 hpγ hγ
    apply max_le
    · have : 1 ≤ Real.exp (γ * (2 * η)) := Real.one_le_exp (by positivity)
      linarith
    · have hp1pos : 0 < p₁ γ := by linarith
      have hB0 := hB0all γ
      calc K γ = B γ * p γ / p₁ γ ^ 2 := rfl
        _ ≤ B γ * p γ / (p γ / 2) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (pow_le_pow_left₀ (by positivity) hp1 2)
        _ = 4 * B γ / p γ := by field_simp; ring
        _ ≤ 4 * Real.exp (γ * (-I + η)) / Real.exp (γ * (-I - η)) :=
            div_le_div₀ (by positivity) (by linarith [hB]) (Real.exp_pos _) hp.1
        _ = 4 * Real.exp (γ * (2 * η)) := by rw [mul_div_assoc, ← Real.exp_sub]; ring_nf
  ------------------------------------------------------------------
  -- Step 8: the conditions of Theorem 3
  have hevA : ∀ᶠ γ in atTop, γ₀ ≤ γ := eventually_ge_atTop γ₀
  have heP : ∀ᶠ γ in atTop, eventProb ν (fun t => A₁ t ∪ A₂ t) γ = p γ := by
    filter_upwards [hevA] with γ hγ
    simp only [eventProb, hA₁e γ hγ, hA₂e γ hγ, hE_union γ]; rfl
  have heP1 : ∀ᶠ γ in atTop, eventProb ν A₁ γ = p₁ γ := by
    filter_upwards [hevA] with γ hγ
    simp only [eventProb, hA₁e γ hγ]; rfl
  have hp0 : Tendsto p atTop (𝓝 0) := by
    have hexp : Tendsto (fun γ => Real.exp (-(γ * (I / 2)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.atTop_mul_const (by linarith) tendsto_id)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall fun γ => ENNReal.toReal_nonneg) ?_
    filter_upwards [hp_bd (I / 2) (by linarith)] with γ h
    calc p γ ≤ _ := h.2
      _ = _ := by congr 1; ring
  have hc1 : Tendsto (fun γ => p₁ γ / p γ) atTop (𝓝 1) := by
    have : Tendsto (fun γ => 1 - p₂ γ / p γ) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hP2
    refine this.congr' ?_
    filter_upwards [hppos] with γ hpγ
    have hsum := hpsum γ
    rw [hsum] at hpγ ⊢
    field_simp
    ring
  have hsub : Tendsto (fun γ => Real.log (n γ : ℝ) / -Real.log (p γ)) atTop (𝓝 0) := by
    have hlogγ : Tendsto (fun γ : ℝ => (Real.log 12 + Real.log γ) / γ) atTop (𝓝 0) := by
      have h1' : Tendsto (fun γ : ℝ => Real.log 12 / γ) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h2' : Tendsto (fun γ : ℝ => Real.log γ / γ) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa [add_div] using h1'.add h2'
    rw [tendsto_order]
    constructor
    · intro e he
      filter_upwards [hp_bd (I / 2) (by linarith), eventually_gt_atTop (0:ℝ)] with γ h hγ
      have hpγ : 0 < p γ := lt_of_lt_of_le (Real.exp_pos _) h.1
      have hlp : Real.log (p γ) < 0 := by
        have := Real.log_le_log hpγ h.2
        rw [Real.log_exp] at this; nlinarith
      have : 0 ≤ Real.log (n γ) / -Real.log (p γ) :=
        div_nonneg (Real.log_nonneg (by exact_mod_cast hn1 γ)) (by linarith)
      linarith
    · intro e he
      set η := min (I / 2) (e * I / 16) with hη_def
      have hη : 0 < η := lt_min (by linarith) (by positivity)
      have hηI : η ≤ I / 2 := min_le_left _ _
      have hηe : η ≤ e * I / 16 := min_le_right _ _
      have hl := hlogγ.eventually (gt_mem_nhds (show (0:ℝ) < e * I / 4 by positivity))
      filter_upwards [hp_bd η hη, hK_bd η hη, hnle, hl, eventually_ge_atTop (1:ℝ)]
        with γ hp hK hn hlγ hγ
      have hpγ : 0 < p γ := lt_of_lt_of_le (Real.exp_pos _) hp.1
      have hlogp : γ * (I - η) ≤ -Real.log (p γ) := by
        have := Real.log_le_log hpγ hp.2
        rw [Real.log_exp] at this; linarith
      have hγ0 : 0 < γ := by linarith
      have hnpos : (0:ℝ) < n γ := by exact_mod_cast hn1 γ
      have hnexp : (n γ : ℝ) ≤ 12 * γ * Real.exp (γ * (2 * η)) := by
        calc (n γ : ℝ) ≤ 3 * (γ * max 1 (K γ)) := hn
          _ ≤ 3 * (γ * (4 * Real.exp (γ * (2 * η)))) := by gcongr
          _ = 12 * γ * Real.exp (γ * (2 * η)) := by ring
      have hlogn : Real.log (n γ) ≤ Real.log 12 + Real.log γ + γ * (2 * η) := by
        calc Real.log (n γ) ≤ Real.log (12 * γ * Real.exp (γ * (2 * η))) :=
              Real.log_le_log hnpos hnexp
          _ = _ := by
              rw [Real.log_mul (by positivity) (by positivity),
                Real.log_mul (by norm_num) (by positivity), Real.log_exp]
      have h12 : Real.log 12 + Real.log γ < γ * (e * I / 4) := by
        rwa [div_lt_iff₀ hγ0, mul_comm] at hlγ
      have hA' : γ * (2 * η) ≤ γ * (e * I / 8) :=
        mul_le_mul_of_nonneg_left (by linarith) hγ0.le
      have hB' : e * (γ * (I - η)) ≤ e * -Real.log (p γ) :=
        mul_le_mul_of_nonneg_left hlogp he.le
      have hC' : e * (γ * (I / 2)) ≤ e * (γ * (I - η)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hγ0.le) he.le
      have hD' : 0 < γ * e * I := by positivity
      rw [div_lt_iff₀ (by nlinarith)]
      nlinarith
  have hc2 : Tendsto (fun γ => variance (eventOutput ν Q A₁ γ) (Q γ) /
      ((n γ : ℝ) * (eventProb ν A₁ γ) ^ 2)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero
      ?_ ?_
    · exact Eventually.of_forall fun γ => div_nonneg (variance_nonneg _ _) (by positivity)
    · filter_upwards [hevA, heP1, hp1half, hppos, eventually_gt_atTop (0:ℝ)]
        with γ hγ he hp1 hpγ hγ0
      rw [he]
      have hp1pos : 0 < p₁ γ := by linarith
      have hn0 : (0:ℝ) < n γ := by exact_mod_cast hn1 γ
      have hv := (hZ1 γ hγ).2
      have hp1le : p₁ γ ≤ p γ := by linarith [hpsum γ, hp₂0 γ]
      have hB0 := hB0all γ
      have hnK : γ * K γ ≤ n γ :=
        le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hγ0.le) (hnge γ)
      have hKge : B γ * p₁ γ ≤ K γ * p₁ γ ^ 2 := by
        simp only [hK_def]
        rw [div_mul_cancel₀ _ (by positivity)]
        nlinarith
      have h3 : γ * (B γ * p₁ γ) ≤ n γ * p₁ γ ^ 2 := by
        calc γ * (B γ * p₁ γ) ≤ γ * (K γ * p₁ γ ^ 2) := mul_le_mul_of_nonneg_left hKge hγ0.le
          _ = (γ * K γ) * p₁ γ ^ 2 := by ring
          _ ≤ n γ * p₁ γ ^ 2 := mul_le_mul_of_nonneg_right hnK (sq_nonneg _)
      rw [div_le_iff₀ (by positivity)]
      calc variance (eventOutput ν Q A₁ γ) (Q γ) ≤ B γ * p₁ γ := hv
        _ = γ⁻¹ * (γ * (B γ * p₁ γ)) := by field_simp
        _ ≤ γ⁻¹ * (n γ * p₁ γ ^ 2) := mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hγ0.le)
  have hc3 : Tendsto (fun γ => (n γ : ℝ) * eventProb Q A₂ γ) atTop (𝓝 0) := by
    have hq2 : ∀ᶠ γ in atTop, eventProb Q A₂ γ ≤ Real.exp (γ * (-c)) := by
      filter_upwards [hevA, (eventually_all_finset S).2 hT2] with γ hγ hT
      simp only [eventProb, hA₂e γ hγ, hQ_def, mixtureIS]
      rw [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.toReal_sum (fun i hi => by
        simp only [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (tilted_ne_top _ _ _))]
      calc ∑ i ∈ S, ((ENNReal.ofReal (α i) • (ν γ).tilted (fun x => inner ℝ (s i) x)) (E₂ γ)).toReal
          = ∑ i ∈ S, α i * ((ν γ).tilted (fun x => inner ℝ (s i) x) (E₂ γ)).toReal :=
            Finset.sum_congr rfl fun i hi => by
              simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hα i hi).le]
        _ ≤ ∑ i ∈ S, α i * Real.exp (γ * (-c)) :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hT i hi) (hα i hi).le
        _ = Real.exp (γ * (-c)) := by rw [← Finset.sum_mul, hα1, one_mul]
    have hlim : Tendsto (fun γ => 48 / c * Real.exp (-(γ * (c / 2)))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.atTop_mul_const (by linarith : (0:ℝ) < c / 2) tendsto_id)).const_mul (48 / c)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · exact Eventually.of_forall fun γ => mul_nonneg (by positivity) ENNReal.toReal_nonneg
    · filter_upwards [hq2, hK_bd (c / 8) (by linarith), hnle, eventually_gt_atTop (0:ℝ)]
        with γ hq hK hn hγ
      have hγexp : γ ≤ 4 / c * Real.exp (γ * (c / 4)) := by
        have := Real.add_one_le_exp (γ * (c / 4))
        rw [div_mul_eq_mul_div, le_div_iff₀ hc]
        nlinarith
      have hnexp : (n γ : ℝ) ≤ 12 * γ * Real.exp (γ * (2 * (c / 8))) := by
        calc (n γ : ℝ) ≤ 3 * (γ * max 1 (K γ)) := hn
          _ ≤ 3 * (γ * (4 * Real.exp (γ * (2 * (c / 8))))) := by gcongr
          _ = 12 * γ * Real.exp (γ * (2 * (c / 8))) := by ring
      have hcomb : Real.exp (γ * (c / 4)) * Real.exp (γ * (2 * (c / 8))) * Real.exp (γ * (-c))
          = Real.exp (-(γ * (c / 2))) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      calc (n γ : ℝ) * eventProb Q A₂ γ
          ≤ (12 * γ * Real.exp (γ * (2 * (c / 8)))) * Real.exp (γ * (-c)) :=
            mul_le_mul hnexp hq ENNReal.toReal_nonneg (by positivity)
        _ ≤ (12 * (4 / c * Real.exp (γ * (c / 4))) * Real.exp (γ * (2 * (c / 8)))) *
              Real.exp (γ * (-c)) := by gcongr
        _ = 48 / c * Real.exp (-(γ * (c / 2))) := by rw [← hcomb]; ring
  ------------------------------------------------------------------
  -- Step 9: apply Theorem 3 and transfer
  have hpA : Tendsto (eventProb ν (fun γ => A₁ γ ∪ A₂ γ)) atTop (𝓝 0) :=
    hp0.congr' (heP.mono fun _ h => h.symm)
  have hc1A : Tendsto (fun γ => eventProb ν A₁ γ / eventProb ν (fun t => A₁ t ∪ A₂ t) γ)
      atTop (𝓝 1) := by
    refine hc1.congr' ?_
    filter_upwards [heP, heP1] with γ h h'
    rw [h, h']
  have hsubA : IsSubexpIn (fun γ => (n γ : ℝ))
      (fun γ => -Real.log (eventProb ν (fun t => A₁ t ∪ A₂ t) γ)) := by
    unfold IsSubexpIn
    refine hsub.congr' ?_
    filter_upwards [heP] with γ h
    rw [h]
  have hL2A : ∀ᶠ γ in atTop, MemLp (eventOutput ν Q A₁ γ) 2 (Q γ) := by
    filter_upwards [hevA] with γ hγ using (hZ1 γ hγ).1
  have T3 := theorem_3 ν Q hQev A₁ A₂ hA₁m hA₂m hAdisj hac hpA hc1A n hn1 hsubA hL2A hc2 hc3
  refine spe_congr Q hQev _ _ _ _ heP ?_ T3.2
  filter_upwards [hevA] with γ hγ
  have := lrOutput_mix ν γ S hSne' α s hα hα1 (hγ₀ γ hγ).2 {x | γ⁻¹ • x ∈ R}
  simp only [eventOutput, hA₁e γ hγ, hA₂e γ hγ, hE_union γ]
  exact this
