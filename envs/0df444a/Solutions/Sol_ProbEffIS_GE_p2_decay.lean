-- Prove2me | solution 1 for ProbEffIS.GE.p2_decay
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:13:43.77734+00:00
-- url     : https://prove2.me/submissions/593c2832-6463-46e9-906f-f44700c2e8b2

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs
import Theorems.Thm_ProbEffIS_GE_halfspace_bound
import Theorems.Thm_ProbEffIS_GE_theorem_2
import Theorems.Thm_ProbEffIS_GE_theorem_1

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE.CH

variable {d : ℕ}

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


/-- Chernoff's bound for a scaled half-space. -/
lemma chernoff_half (P : Measure (Rd d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : 0 < γ)
    (θ c : Rd d) (hint : Integrable (fun y => Real.exp (inner ℝ θ y)) P) :
    (P {x | γ⁻¹ • x ∈ halfspace θ c}).toReal ≤
      (∫ y, Real.exp (inner ℝ θ y) ∂P) * Real.exp (-(γ * inner ℝ θ c)) := by
  have hA : MeasurableSet {x : Rd d | γ⁻¹ • x ∈ halfspace θ c} :=
    (continuous_const_smul γ⁻¹).measurable ((isClosed_le continuous_const
      (continuous_const.inner (continuous_id.sub continuous_const))).measurableSet)
  rw [← integral_mul_const, ← measureReal_def, ← integral_indicator_one hA]
  refine integral_mono ((integrable_const 1).indicator hA) (hint.mul_const _) fun x => ?_
  by_cases hx : x ∈ {x : Rd d | γ⁻¹ • x ∈ halfspace θ c}
  · rw [Set.indicator_of_mem hx, Pi.one_apply, ← Real.exp_add]
    apply Real.one_le_exp
    have h0 : 0 ≤ inner ℝ θ (γ⁻¹ • x - c) := hx
    rw [inner_sub_right, inner_smul_right] at h0
    have := mul_le_mul_of_nonneg_left
      (show inner ℝ θ c ≤ γ⁻¹ * inner ℝ θ x by linarith) hγ.le
    rw [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul] at this
    linarith
  · rw [Set.indicator_of_notMem hx]; positivity

/-- Exponential decay of a scaled half-space probability at the Chernoff rate. -/
lemma half_decay (ν : ℝ → Measure (Rd d)) [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (θ c : Rd d) (M : ℝ) (hM : μ θ = (M : EReal)) :
    ∀ η > 0, ∀ᶠ γ in atTop, (ν γ {x | γ⁻¹ • x ∈ halfspace θ c}).toReal ≤
      Real.exp (γ * (-(inner ℝ θ c - M) + η)) := by
  intro η hη
  have ht := h1.tendsto θ
  rw [hM] at ht
  obtain ⟨hJ, hlim⟩ := rate_real
    (fun γ => ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ θ y)) ∂(ν γ)) M ht
  have hint : ∀ᶠ γ in atTop, Integrable (fun y => Real.exp (inner ℝ θ y)) (ν γ) := by
    filter_upwards [hJ] with γ ⟨_, hlt⟩
    refine ⟨(Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simpa [Real.enorm_eq_ofReal (Real.exp_pos _).le] using hlt
  have hlt := hlim.eventually (gt_mem_nhds (show M < M + η by linarith))
  filter_upwards [hint, hlt, eventually_gt_atTop (0:ℝ)] with γ hγi hγl hγ
  have hZ : ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ) =
      (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ θ y)) ∂(ν γ)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => (Real.exp_pos _).le) hγi.1
  have hZpos : 0 < ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ) := integral_exp_pos hγi
  rw [← hZ] at hγl
  have hZle : ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ) ≤ Real.exp (γ * (M + η)) := by
    have hl : Real.log (∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) < γ * (M + η) := by
      rw [inv_mul_lt_iff₀ hγ] at hγl; exact hγl
    exact (Real.log_lt_iff_lt_exp hZpos |>.1 hl).le
  calc (ν γ {x | γ⁻¹ • x ∈ halfspace θ c}).toReal
      ≤ (∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) * Real.exp (-(γ * inner ℝ θ c)) :=
        chernoff_half (ν γ) γ hγ θ c hγi
    _ ≤ Real.exp (γ * (M + η)) * Real.exp (-(γ * inner ℝ θ c)) :=
        mul_le_mul_of_nonneg_right hZle (Real.exp_pos _).le
    _ = Real.exp (γ * (-(inner ℝ θ c - M) + η)) := by rw [← Real.exp_add]; ring_nf

/-- Converting eventual exponential bounds into an `EReal` limsup bound. -/
lemma limsup_le_of_exp (m : ℝ → ENNReal) (hm : ∀ γ, m γ ≠ ⊤) (L : ℝ)
    (h : ∀ η > 0, ∀ᶠ γ in atTop, (m γ).toReal ≤ Real.exp (γ * (L + η))) :
    limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) * ENNReal.log (m γ)) atTop ≤ (L : EReal) := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  rw [EReal.coe_lt_coe_iff] at hz
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [h (z - L) (by linarith), eventually_gt_atTop (0:ℝ)] with γ hγ hγ0
  have hγ' : (0:ℝ) < γ⁻¹ := inv_pos.2 hγ0
  rcases eq_or_ne (m γ) 0 with h0 | h0
  · rw [h0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hγ']; exact bot_le
  have hr : 0 < (m γ).toReal := ENNReal.toReal_pos h0 (hm γ)
  rw [← ENNReal.ofReal_toReal (hm γ), ENNReal.log_ofReal_of_pos hr, ← EReal.coe_mul,
    EReal.coe_le_coe_iff]
  have hl : Real.log (m γ).toReal ≤ γ * (L + (z - L)) := by
    have := Real.log_le_log hr hγ
    rwa [Real.log_exp] at this
  rw [inv_mul_le_iff₀ hγ0]
  linarith

/-- The rate function is nonnegative for probability laws. -/
lemma rate_nonneg (ν : ℝ → Measure (Rd d)) [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (y : Rd d) : 0 ≤ rate μ y := by
  have hμ0 : μ 0 = 0 := by
    have ht := h1.tendsto 0
    have : ∀ γ, scaledLogMGF ν γ 0 = 0 := fun γ => by simp [scaledLogMGF]
    simp only [this] at ht
    exact (tendsto_nhds_unique ht tendsto_const_nhds)
  have := le_iSup (fun x => ((inner ℝ x y : ℝ) : EReal) - μ x) 0
  simp only [hμ0, inner_zero_left, EReal.coe_zero, sub_zero] at this
  exact this

/-- The selected (most significant) rate and the next rate, in real form. -/
lemma rates_setup {r : ℕ} (ν : ℝ → Measure (Rd d)) [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (h2 : Assumption2 μ R)
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s)
    (S : Finset (Fin r)) (hS : IsMostSignificant μ a S) :
    ∃ M : Fin r → ℝ, (∀ j, μ (s j) = (M j : EReal)) ∧
      (∀ j, rate μ (a j) = ((inner ℝ (s j) (a j) - M j : ℝ) : EReal)) ∧
      (∀ i ∈ S, rate μ (a i) = rateOn μ R) := by
  have hhalf : ∀ j, rate μ (a j) = ((inner ℝ (s j) (a j) : ℝ) : EReal) - μ (s j) := fun j =>
    (halfspace_bound ν μ h1 (s j) (a j) (hA.tilt_mem j) (hA.grad_eq j)).1
  have hrate_top : ∀ j, rate μ (a j) < ⊤ := fun j =>
    (interior_subset (hA.mem_interior_dom_rate j) : a j ∈ dom (rate μ))
  have hμtop : ∀ j, μ (s j) ≠ ⊤ := fun j => (interior_subset (hA.tilt_mem j) : s j ∈ dom μ).ne
  have hμbot : ∀ j, μ (s j) ≠ ⊥ := by
    intro j h
    have := hrate_top j
    rw [hhalf j, h, EReal.coe_sub_bot] at this
    exact lt_irrefl _ this
  refine ⟨fun j => (μ (s j)).toReal, fun j => (EReal.coe_toReal (hμtop j) (hμbot j)).symm,
    fun j => ?_, fun i hi => ?_⟩
  · rw [hhalf j, EReal.coe_sub, EReal.coe_toReal (hμtop j) (hμbot j)]
  · obtain ⟨hSne, hSeq, hSlt⟩ := hS
    obtain ⟨i₀, hi₀R, hi₀min⟩ := theorem_2 ν μ h1 R h2 a s hA
    by_cases h0 : i₀ ∈ S
    · rw [hi₀R]; exact hSeq i hi i₀ h0
    · exact absurd (hi₀min i) (not_le.2 (hSlt i hi i₀ h0))

/-- The omitted region lies in the half-spaces of the omitted points. -/
lemma splitOut_subset {r : ℕ} (μ : Rd d → EReal) (R : Set (Rd d))
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s) (S : Finset (Fin r)) (y : Rd d)
    (hy : y ∈ splitOut R S a s) : ∃ j ∈ Finset.univ \ S, y ∈ halfspace (s j) (a j) := by
  obtain ⟨hyR, hyn⟩ := hy
  have := hA.cover hyR
  simp only [Set.mem_iUnion] at this
  obtain ⟨j, hj⟩ := this
  refine ⟨j, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun hjS => hyn ⟨hyR, ?_⟩⟩, hj⟩
  simp only [Set.mem_iUnion]
  exact ⟨j, hjS, hj⟩

/-- Decay of the omitted region at rate `Iout`. -/
lemma out_decay {r : ℕ} (ν : ℝ → Measure (Rd d)) [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s)
    (S : Finset (Fin r)) (M : Fin r → ℝ) (hM : ∀ j, μ (s j) = (M j : EReal))
    (J : ℝ) (hJ : ∀ j ∈ Finset.univ \ S, J ≤ inner ℝ (s j) (a j) - M j) :
    ∀ η > 0, ∀ᶠ γ in atTop, (ν γ {x | γ⁻¹ • x ∈ splitOut R S a s}).toReal ≤
      Real.exp (γ * (-J + η)) := by
  intro η hη
  set T := Finset.univ \ S
  have hC : ∀ᶠ γ in atTop, (T.card : ℝ) ≤ Real.exp (γ * (η / 2)) :=
    (Real.tendsto_exp_atTop.comp (Tendsto.atTop_mul_const (by linarith) tendsto_id)).eventually_ge_atTop _
  have hj : ∀ j ∈ T, ∀ᶠ γ in atTop, (ν γ {x | γ⁻¹ • x ∈ halfspace (s j) (a j)}).toReal ≤
      Real.exp (γ * (-J + η / 2)) := by
    intro j hjT
    filter_upwards [half_decay ν μ h1 (s j) (a j) (M j) (hM j) (η / 2) (by linarith),
      eventually_gt_atTop (0:ℝ)] with γ h hγ
    refine h.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hγ.le))
    linarith [hJ j hjT]
  filter_upwards [(eventually_all_finset T).2 hj, hC, eventually_gt_atTop (0:ℝ)] with γ hγ hCγ hγ0
  have hsub : {x : Rd d | γ⁻¹ • x ∈ splitOut R S a s} ⊆
      ⋃ j ∈ T, {x | γ⁻¹ • x ∈ halfspace (s j) (a j)} := by
    intro x hx
    obtain ⟨j, hjT, hj⟩ := splitOut_subset μ R a s hA S _ hx
    simp only [Set.mem_iUnion]
    exact ⟨j, hjT, hj⟩
  have hmeas : (ν γ {x | γ⁻¹ • x ∈ splitOut R S a s}) ≤
      ∑ j ∈ T, ν γ {x | γ⁻¹ • x ∈ halfspace (s j) (a j)} :=
    (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  calc (ν γ {x | γ⁻¹ • x ∈ splitOut R S a s}).toReal
      ≤ (∑ j ∈ T, ν γ {x | γ⁻¹ • x ∈ halfspace (s j) (a j)}).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun _ _ => measure_ne_top _ _) hmeas
    _ = ∑ j ∈ T, (ν γ {x | γ⁻¹ • x ∈ halfspace (s j) (a j)}).toReal :=
        ENNReal.toReal_sum fun _ _ => measure_ne_top _ _
    _ ≤ ∑ j ∈ T, Real.exp (γ * (-J + η / 2)) := Finset.sum_le_sum hγ
    _ = (T.card : ℝ) * Real.exp (γ * (-J + η / 2)) := by simp
    _ ≤ Real.exp (γ * (η / 2)) * Real.exp (γ * (-J + η / 2)) :=
        mul_le_mul_of_nonneg_right hCγ (Real.exp_pos _).le
    _ = Real.exp (γ * (-J + η)) := by rw [← Real.exp_add]; ring_nf

end ProbEffIS.GE.CH

open ProbEffIS.GE ProbEffIS.GE.CH in
theorem solution {d r : ℕ} (ν : ℝ → Measure (Rd d))
    [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (h2 : Assumption2 μ R)
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s)
    (S : Finset (Fin r)) (hS : IsMostSignificant μ a S)
    (hSne : S ≠ Finset.univ) :
    let Iout : EReal := ⨅ j ∈ (Finset.univ \ S), rate μ (a j)
    limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
      ENNReal.log (ν γ {x | γ⁻¹ • x ∈ splitOut R S a s})) atTop ≤ -Iout ∧
    -Iout < -(rateOn μ R) ∧
    Tendsto (fun γ => rareProb ν γ (splitOut R S a s) / rareProb ν γ R)
      atTop (𝓝 0) := by
  intro Iout
  obtain ⟨M, hM, hrate, hrateS⟩ := rates_setup ν μ h1 R h2 a s hA S hS
  set T := Finset.univ \ S with hT_def
  have hT : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    exact hSne (Finset.eq_univ_of_forall fun x => h (Finset.mem_univ x))
  set L : Fin r → ℝ := fun j => inner ℝ (s j) (a j) - M j with hL_def
  set J : ℝ := T.inf' hT L with hJ_def
  have hJle : ∀ j ∈ T, J ≤ inner ℝ (s j) (a j) - M j := fun j hj => Finset.inf'_le L hj
  obtain ⟨j₀, hj₀, hj₀eq⟩ := Finset.exists_mem_eq_inf' hT L
  have hIout : Iout = (J : EReal) := by
    apply le_antisymm
    · calc Iout ≤ rate μ (a j₀) := iInf₂_le j₀ hj₀
        _ = (J : EReal) := by rw [hrate j₀, hJ_def, hj₀eq]
    · exact le_iInf₂ fun j hj => by rw [hrate j]; exact EReal.coe_le_coe_iff.2 (hJle j hj)
  obtain ⟨i₁, hi₁⟩ := hS.1
  set I : ℝ := L i₁ with hI_def
  have hI : rateOn μ R = (I : EReal) := by rw [← hrateS i₁ hi₁, hrate i₁]
  have hIJ : I < J := by
    have := hS.2.2 i₁ hi₁ j₀ (Finset.mem_sdiff.1 hj₀).2
    rw [hrate i₁, hrate j₀] at this
    rw [hJ_def, hj₀eq]; exact EReal.coe_lt_coe_iff.1 this
  have hdecay := out_decay ν μ h1 R a s hA S M hM J hJle
  refine ⟨?_, ?_, ?_⟩
  · rw [hIout, ← EReal.coe_neg]
    refine limsup_le_of_exp _ (fun γ => measure_ne_top _ _) (-J) fun η hη => ?_
    filter_upwards [hdecay η hη] with γ h
    exact h
  · rw [hIout, hI]; exact EReal.neg_lt_neg_iff.2 (EReal.coe_lt_coe_iff.2 hIJ)
  · have ht := (theorem_1 ν (Eventually.of_forall inferInstance) μ h1 R h2.measurable).2.2
      h2 r a s hA
    rw [hI, ← EReal.coe_neg] at ht
    obtain ⟨hm, hlim⟩ := rate_real (fun γ => ν γ {x | γ⁻¹ • x ∈ R}) (-I) ht
    set η : ℝ := (J - I) / 4 with hη_def
    have hη : 0 < η := by rw [hη_def]; linarith
    have hlow : ∀ᶠ γ in atTop, Real.exp (γ * (-I - η)) ≤ rareProb ν γ R := by
      filter_upwards [hm, hlim.eventually (lt_mem_nhds (show -I - η < -I by linarith)),
        eventually_gt_atTop (0:ℝ)] with γ ⟨h0, htop⟩ hl hγ
      have hp : 0 < rareProb ν γ R := ENNReal.toReal_pos h0.ne' htop.ne
      rw [← Real.exp_log hp]
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hl.le hγ.le
      rwa [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul] at this
    have hlim0 : Tendsto (fun γ => Real.exp (-(γ * (2 * η)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.atTop_mul_const (by linarith) tendsto_id)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim0
      (Eventually.of_forall fun γ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ?_
    filter_upwards [hlow, hdecay η hη] with γ hl hu
    have hpos : 0 < Real.exp (γ * (-I - η)) := Real.exp_pos _
    calc rareProb ν γ (splitOut R S a s) / rareProb ν γ R
        ≤ Real.exp (γ * (-J + η)) / Real.exp (γ * (-I - η)) :=
          div_le_div₀ (Real.exp_pos _).le hu hpos hl
      _ = Real.exp (-(γ * (2 * η))) := by
          rw [← Real.exp_sub]; congr 1; rw [hη_def]; ring
