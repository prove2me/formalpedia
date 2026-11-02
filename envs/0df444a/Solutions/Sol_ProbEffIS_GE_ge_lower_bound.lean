-- Prove2me | solution 1 for ProbEffIS.GE.ge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:41:48.588672+00:00
-- url     : https://prove2.me/submissions/4547a6fa-22a3-4d4d-ad8c-7f3829ed7ba7

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs
import Theorems.Thm_ProbEffIS_GE_halfspace_bound

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE.LB

variable {d : ℕ}

/-- Hölder's inequality for the moment generating function. -/
lemma mgf_holder (m : Measure (Rd d)) (u v : Rd d) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ ((1 - t) • u + t • v) y)) ∂m ≤
      (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ u y)) ∂m) ^ (1 - t) *
      (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ v y)) ∂m) ^ t := by
  have h1t : 0 < 1 - t := by linarith
  set f : Rd d → ENNReal := fun y => ENNReal.ofReal (Real.exp (inner ℝ u y)) ^ (1 - t)
  set g : Rd d → ENNReal := fun y => ENNReal.ofReal (Real.exp (inner ℝ v y)) ^ t
  have hcont : ∀ w : Rd d, Continuous fun y : Rd d => Real.exp (inner ℝ w y) := fun w =>
    Real.continuous_exp.comp (continuous_const.inner continuous_id)
  have hf : AEMeasurable f m :=
    ((ENNReal.continuous_ofReal.comp (hcont u)).measurable.pow_const _).aemeasurable
  have hg : AEMeasurable g m :=
    ((ENNReal.continuous_ofReal.comp (hcont v)).measurable.pow_const _).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq m
    (Real.holderConjugate_one_div h1t ht0 (by ring)) hf hg
  have hfg : ∀ y, (f * g) y = ENNReal.ofReal (Real.exp (inner ℝ ((1 - t) • u + t • v) y)) := by
    intro y
    simp only [Pi.mul_apply, f, g]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h1t.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht0.le, ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, inner_add_left, inner_smul_left,
      inner_smul_left]
    congr 2
    simp only [RCLike.conj_to_real]
    ring
  have hfp : ∀ y, f y ^ (1 / (1 - t)) = ENNReal.ofReal (Real.exp (inner ℝ u y)) := by
    intro y
    simp only [f]
    rw [← ENNReal.rpow_mul, mul_one_div_cancel h1t.ne', ENNReal.rpow_one]
  have hgq : ∀ y, g y ^ (1 / t) = ENNReal.ofReal (Real.exp (inner ℝ v y)) := by
    intro y
    simp only [g]
    rw [← ENNReal.rpow_mul, mul_one_div_cancel ht0.ne', ENNReal.rpow_one]
  simp only [hfg, hfp, hgq, one_div_one_div] at hH
  exact hH

/-- Convexity of the scaled log-MGF for a fixed positive parameter. -/
lemma slmgf_convex (ν : ℝ → Measure (Rd d)) (γ : ℝ) (hγ : 0 < γ) (u v : Rd d) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    scaledLogMGF ν γ ((1 - t) • u + t • v) ≤
      ((1 - t : ℝ) : EReal) * scaledLogMGF ν γ u + (t : EReal) * scaledLogMGF ν γ v := by
  unfold scaledLogMGF
  have hγ' : (0 : EReal) ≤ ((γ⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 hγ).le
  calc ((γ⁻¹ : ℝ) : EReal) * ENNReal.log
        (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ ((1 - t) • u + t • v) y)) ∂(ν γ))
      ≤ ((γ⁻¹ : ℝ) : EReal) * ENNReal.log
        ((∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ u y)) ∂(ν γ)) ^ (1 - t) *
          (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ v y)) ∂(ν γ)) ^ t) :=
        mul_le_mul_of_nonneg_left (ENNReal.log_monotone (mgf_holder _ u v t ht0 ht1)) hγ'
    _ = _ := by
        rw [ENNReal.log_mul_add, ENNReal.log_rpow, ENNReal.log_rpow,
          EReal.left_distrib_of_nonneg_of_ne_top hγ' (EReal.coe_ne_top _), mul_left_comm,
          mul_left_comm ((γ⁻¹ : ℝ) : EReal)]


lemma coe_mul_ne_top {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) : (c : EReal) * x ≠ ⊤ := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hc]; exact bot_ne_top
  | coe x => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

/-- Convexity of the limiting log-MGF on its effective domain. -/
lemma mu_convex (ν : ℝ → Measure (Rd d)) (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (u v : Rd d) (hu : μ u ≠ ⊤) (hv : μ v ≠ ⊤) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    μ ((1 - t) • u + t • v) ≤ ((1 - t : ℝ) : EReal) * μ u + (t : EReal) * μ v := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hA := EReal.Tendsto.const_mul (h1.tendsto u) (a := ((1 - t : ℝ) : EReal))
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hB := EReal.Tendsto.const_mul (h1.tendsto v) (a := ((t : ℝ) : EReal))
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hR := (EReal.continuousAt_add (p := (((1 - t : ℝ) : EReal) * μ u, ((t : ℝ) : EReal) * μ v))
    (Or.inl (coe_mul_ne_top h1t hu)) (Or.inr (coe_mul_ne_top ht0 hv))).tendsto.comp
    (hA.prodMk_nhds hB)
  refine le_of_tendsto_of_tendsto (h1.tendsto _) hR ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
  exact slmgf_convex ν γ hγ u v t ht0 ht1

/-- An eventual bound on the moment generating function from a bound on `μ`. -/
lemma mgf_bound (ν : ℝ → Measure (Rd d)) (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (θ : Rd d) (M : ℝ) (hM : μ θ < (M : EReal)) :
    ∀ᶠ γ in atTop, Integrable (fun y => Real.exp (inner ℝ θ y)) (ν γ) ∧
      ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ) ≤ Real.exp (γ * M) := by
  have h := (h1.tendsto θ).eventually (gt_mem_nhds hM)
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with γ hγ hγ0
  unfold scaledLogMGF at hγ
  set J := ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ θ y)) ∂(ν γ) with hJ_def
  have hγ' : (0:ℝ) < γ⁻¹ := inv_pos.2 hγ0
  have hJtop : J ≠ ⊤ := by
    intro hJ
    rw [hJ, ENNReal.log_top, EReal.coe_mul_top_of_pos hγ'] at hγ
    exact absurd hγ (not_lt.2 le_top)
  have hint : Integrable (fun y => Real.exp (inner ℝ θ y)) (ν γ) := by
    refine ⟨(Real.continuous_exp.comp (continuous_const.inner continuous_id)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simpa [Real.enorm_eq_ofReal (Real.exp_pos _).le] using hJtop.lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => (Real.exp_pos _).le) hint.1]
  rw [← hJ_def]
  rcases eq_or_ne J 0 with h0 | h0
  · rw [h0]; simp only [ENNReal.toReal_zero]; positivity
  have hr : 0 < J.toReal := ENNReal.toReal_pos h0 hJtop
  rw [← ENNReal.ofReal_toReal hJtop, ENNReal.log_ofReal_of_pos hr, ← EReal.coe_mul,
    EReal.coe_lt_coe_iff] at hγ
  have : Real.log J.toReal < γ * M := by rw [inv_mul_lt_iff₀ hγ0] at hγ; exact hγ
  exact (Real.log_lt_iff_lt_exp hr |>.1 this).le

/-- Chernoff's bound for a scaled half-space. -/
lemma chernoff (P : Measure (Rd d)) [IsFiniteMeasure P] (γ : ℝ) (hγ : 0 < γ) (θ : Rd d) (c : ℝ)
    (hint : Integrable (fun y => Real.exp (inner ℝ θ y)) P) :
    (P {x | c ≤ inner ℝ θ (γ⁻¹ • x)}).toReal ≤
      (∫ y, Real.exp (inner ℝ θ y) ∂P) * Real.exp (-(γ * c)) := by
  have hA : MeasurableSet {x : Rd d | c ≤ inner ℝ θ (γ⁻¹ • x)} :=
    measurableSet_le measurable_const
      ((continuous_const.inner (continuous_const_smul γ⁻¹)).measurable)
  rw [← integral_mul_const, ← measureReal_def, ← integral_indicator_one hA]
  refine integral_mono ((integrable_const 1).indicator hA) (hint.mul_const _) fun x => ?_
  by_cases hx : x ∈ {x : Rd d | c ≤ inner ℝ θ (γ⁻¹ • x)}
  · rw [Set.indicator_of_mem hx, Pi.one_apply, ← Real.exp_add]
    apply Real.one_le_exp
    have h0 : c ≤ inner ℝ θ (γ⁻¹ • x) := hx
    rw [inner_smul_right] at h0
    have := mul_le_mul_of_nonneg_left h0 hγ.le
    rw [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul] at this
    linarith
  · rw [Set.indicator_of_notMem hx]; positivity


/-- An eventual lower bound on the moment generating function. -/
lemma mgf_lower (ν : ℝ → Measure (Rd d)) (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (θ : Rd d) (M : ℝ) (hM : (M : EReal) < μ θ) :
    ∀ᶠ γ in atTop, Integrable (fun y => Real.exp (inner ℝ θ y)) (ν γ) →
      Real.exp (γ * M) ≤ ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ) := by
  have h := (h1.tendsto θ).eventually (lt_mem_nhds hM)
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with γ hγ hγ0 hint
  unfold scaledLogMGF at hγ
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => (Real.exp_pos _).le) hint.1]
  set J := ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ θ y)) ∂(ν γ) with hJ_def
  have hγ' : (0:ℝ) < γ⁻¹ := inv_pos.2 hγ0
  have hJtop : J ≠ ⊤ := by
    have := hint.2
    unfold HasFiniteIntegral at this
    simpa [hJ_def, Real.enorm_eq_ofReal (Real.exp_pos _).le] using this.ne
  have h0 : J ≠ 0 := by
    intro h0
    rw [h0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hγ'] at hγ
    exact absurd hγ (not_lt.2 bot_le)
  have hr : 0 < J.toReal := ENNReal.toReal_pos h0 hJtop
  rw [← ENNReal.ofReal_toReal hJtop, ENNReal.log_ofReal_of_pos hr, ← EReal.coe_mul,
    EReal.coe_lt_coe_iff] at hγ
  have : γ * M < Real.log J.toReal := by rw [lt_inv_mul_iff₀ hγ0] at hγ; exact hγ
  exact (Real.lt_log_iff_exp_lt hr |>.1 this).le

lemma mu_zero (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) : μ 0 = 0 := by
  have ht := h1.tendsto 0
  have : ∀ᶠ γ in atTop, scaledLogMGF ν γ 0 = 0 := by
    filter_upwards [hν] with γ hP
    simp [scaledLogMGF]
  exact tendsto_nhds_unique (ht.congr' this) tendsto_const_nhds

lemma mu_ne_bot (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (θ : Rd d) : μ θ ≠ ⊥ := by
  intro hb
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h1.zero_mem
  set s : ℝ := r / (2 * (‖θ‖ + 1)) with hs
  have hs0 : 0 < s := by positivity
  have hmem : (-s) • θ ∈ Metric.ball (0 : Rd d) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hs0, hs]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg θ]
  have htop : μ ((-s) • θ) ≠ ⊤ := (interior_subset (hball hmem) : _ ∈ dom μ).ne
  have hc := mu_convex ν μ h1 θ ((-s) • θ) (by rw [hb]; exact bot_ne_top) htop
    (1 / (1 + s)) (by positivity) (by rw [div_lt_one (by linarith)]; linarith)
  have heq : (1 - 1 / (1 + s)) • θ + (1 / (1 + s)) • ((-s) • θ) = 0 := by
    rw [smul_smul, ← add_smul]
    have : (1 - 1 / (1 + s)) + 1 / (1 + s) * -s = 0 := by field_simp; ring
    rw [this, zero_smul]
  rw [heq, hb, mu_zero ν hν μ h1, EReal.coe_mul_bot_of_pos (by
    have : (1:ℝ) / (1 + s) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith), EReal.bot_add] at hc
  exact absurd hc (not_le.2 EReal.bot_lt_zero)


/-- Chernoff's bound for an exponential tilt of the law. -/
lemma tilt_chernoff (P : Measure (Rd d)) [IsProbabilityMeasure P] (γ : ℝ) (hγ : 0 < γ)
    (θ w : Rd d) (c : ℝ) (hθ : Integrable (fun y => Real.exp (inner ℝ θ y)) P)
    (hθw : Integrable (fun y => Real.exp (inner ℝ (θ + w) y)) P) :
    ((P.tilted (fun x => inner ℝ θ x)) {x | c ≤ inner ℝ w (γ⁻¹ • x)}).toReal ≤
      (∫ y, Real.exp (inner ℝ (θ + w) y) ∂P) / (∫ y, Real.exp (inner ℝ θ y) ∂P) *
        Real.exp (-(γ * c)) := by
  have := isProbabilityMeasure_tilted hθ
  have hint : Integrable (fun y => Real.exp (inner ℝ w y)) (P.tilted (fun x => inner ℝ θ x)) := by
    rw [integrable_tilted_iff hθ]
    refine hθw.congr (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, ← Real.exp_add, inner_add_left]
  have h := chernoff (P.tilted (fun x => inner ℝ θ x)) γ hγ w c hint
  rw [integral_exp_tilted] at h
  convert h using 3
  congr 1
  funext x
  simp only [Pi.add_apply, inner_add_left]

/-- The local lower bound around an exposed point, via exponential tilting. -/
lemma tilt_llb (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (θ : Rd d) (hθ : θ ∈ interior (dom μ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ η > 0, ∀ᶠ γ in atTop,
      Real.exp (γ * ((μ θ).toReal - inner ℝ θ (gradE μ θ) - ‖θ‖ * δ - η)) ≤
        (ν γ {x | γ⁻¹ • x ∈ Metric.ball (gradE μ θ) δ}).toReal := by
  intro η hη
  set a := gradE μ θ with ha_def
  set f : Rd d → ℝ := fun y => (μ y).toReal with hf_def
  have hD : interior (dom μ) ∈ 𝓝 θ := isOpen_interior.mem_nhds hθ
  have hdiff : HasFDerivAt f (InnerProductSpace.toDual ℝ (Rd d) a) θ :=
    (h1.differentiableOn.differentiableAt hD).hasGradientAt.hasFDerivAt
  have hfin : ∀ w ∈ interior (dom μ), μ w = ((f w : ℝ) : EReal) := fun w hw =>
    (EReal.coe_toReal (interior_subset hw : w ∈ dom μ).ne (mu_ne_bot ν hν μ h1 w)).symm
  set c : ℝ := δ / (d + 1) with hc_def
  have hc : 0 < c := by positivity
  have hev : ∀ᶠ w in 𝓝 θ, ‖f w - f θ - (InnerProductSpace.toDual ℝ (Rd d) a) (w - θ)‖ ≤
      (c / 4) * ‖w - θ‖ := hdiff.isLittleO.def (by positivity)
  obtain ⟨r0, hr0, hr0s⟩ := Metric.mem_nhds_iff.1 (inter_mem hev hD)
  set t : ℝ := r0 / 2 with ht_def
  have ht : 0 < t := by positivity
  have hstep : ∀ e : Rd d, ‖e‖ = 1 → θ + t • e ∈ interior (dom μ) ∧
      f (θ + t • e) ≤ f θ + t * inner ℝ a e + t * (c / 4) := by
    intro e he
    have hmem : θ + t • e ∈ Metric.ball θ r0 := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
        Real.norm_eq_abs, abs_of_pos ht]
      linarith
    obtain ⟨h1', h2'⟩ := hr0s hmem
    refine ⟨h2', ?_⟩
    simp only [Set.mem_ofPred_eq, add_sub_cancel_left, InnerProductSpace.toDual_apply_apply,
      norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos ht, inner_smul_right] at h1'
    have := le_abs_self (f (θ + t • e) - f θ - t * inner ℝ a e)
    nlinarith
  -- the 2d directions
  have hunit : ∀ (k : Fin d) (σ : ℝ), |σ| = 1 → ‖EuclideanSpace.single k σ‖ = 1 := by
    intro k σ hσ; rw [PiLp.norm_single, Real.norm_eq_abs, hσ]
  set η₁ : ℝ := min (t * c / 8) (η / 4) with hη₁
  have hη₁0 : 0 < η₁ := lt_min (by positivity) (by positivity)
  have hη₁a : η₁ ≤ t * c / 8 := min_le_left _ _
  have hη₁b : η₁ ≤ η / 4 := min_le_right _ _
  -- eventual bounds for the moment generating functions
  have hdirev : ∀ σ : ℝ, |σ| = 1 → ∀ k : Fin d, ∀ᶠ γ in atTop,
      Integrable (fun y => Real.exp (inner ℝ (θ + t • EuclideanSpace.single k σ) y)) (ν γ) ∧
      ∫ y, Real.exp (inner ℝ (θ + t • EuclideanSpace.single k σ) y) ∂(ν γ) ≤
        Real.exp (γ * (f (θ + t • EuclideanSpace.single k σ) + η₁)) := by
    intro σ hσ k
    obtain ⟨hmem, -⟩ := hstep _ (hunit k σ hσ)
    refine mgf_bound ν μ h1 _ _ ?_
    rw [hfin _ hmem, EReal.coe_lt_coe_iff]; linarith
  have hθev : ∀ᶠ γ in atTop, Integrable (fun y => Real.exp (inner ℝ θ y)) (ν γ) ∧
      ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ) ≤ Real.exp (γ * (f θ + 1)) :=
    mgf_bound ν μ h1 θ (f θ + 1) (by rw [hfin θ hθ, EReal.coe_lt_coe_iff]; linarith)
  have hθlow := mgf_lower ν μ h1 θ (f θ - η₁) (by rw [hfin θ hθ, EReal.coe_lt_coe_iff]; linarith)
  have hsmall : ∀ᶠ γ in atTop, (2 * d : ℝ) * Real.exp (-(γ * (t * c / 2))) ≤ 1 / 2 := by
    have : Tendsto (fun γ : ℝ => (2 * d : ℝ) * Real.exp (-(γ * (t * c / 2)))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.atTop_mul_const (by positivity : (0:ℝ) < t * c / 2) tendsto_id)).const_mul
        (2 * d : ℝ)
      simpa using this
    exact this.eventually (ge_mem_nhds (by norm_num))
  have hhalf : ∀ᶠ γ in atTop, Real.exp (-(γ * (3 * η / 4))) ≤ 1 / 2 := by
    have : Tendsto (fun γ : ℝ => Real.exp (-(γ * (3 * η / 4)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.atTop_mul_const (by positivity) tendsto_id)
    exact this.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hν, hθev, hθlow, hsmall, hhalf, eventually_gt_atTop (0:ℝ),
    (eventually_all_finset Finset.univ).2 (fun k _ => hdirev 1 (by norm_num) k),
    (eventually_all_finset Finset.univ).2 (fun k _ => hdirev (-1) (by norm_num) k)]
    with γ hP hθe hθl hsm hhf hγ hpos hneg
  have hθi := hθe.1
  have hZ := hθl hθi
  have hZpos : 0 < ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ) := integral_exp_pos hθi
  set Q := (ν γ).tilted (fun x => inner ℝ θ x) with hQ_def
  have hQprob : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hθi
  set U := {x : Rd d | γ⁻¹ • x ∈ Metric.ball a δ} with hU_def
  have hUm : MeasurableSet U := (continuous_const_smul γ⁻¹).measurable Metric.isOpen_ball.measurableSet
  -- each direction has small tilted probability
  have hdirQ : ∀ σ : ℝ, |σ| = 1 → ∀ k : Fin d,
      (∀ k' ∈ (Finset.univ : Finset (Fin d)),
        Integrable (fun y => Real.exp (inner ℝ (θ + t • EuclideanSpace.single k' σ) y)) (ν γ) ∧
        ∫ y, Real.exp (inner ℝ (θ + t • EuclideanSpace.single k' σ) y) ∂(ν γ) ≤
          Real.exp (γ * (f (θ + t • EuclideanSpace.single k' σ) + η₁))) →
      (Q {x | t * (inner ℝ (EuclideanSpace.single k σ) a + c) ≤
          inner ℝ (t • EuclideanSpace.single k σ) (γ⁻¹ • x)}).toReal ≤
        Real.exp (-(γ * (t * c / 2))) := by
    intro σ hσ k hall
    obtain ⟨hi, hle⟩ := hall k (Finset.mem_univ _)
    obtain ⟨-, hf⟩ := hstep _ (hunit k σ hσ)
    have h := tilt_chernoff (ν γ) γ hγ θ (t • EuclideanSpace.single k σ)
      (t * (inner ℝ (EuclideanSpace.single k σ) a + c)) hθi hi
    refine h.trans ?_
    calc (∫ y, Real.exp (inner ℝ (θ + t • EuclideanSpace.single k σ) y) ∂(ν γ)) /
          (∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) *
          Real.exp (-(γ * (t * (inner ℝ (EuclideanSpace.single k σ) a + c))))
        ≤ Real.exp (γ * (f (θ + t • EuclideanSpace.single k σ) + η₁)) /
            Real.exp (γ * (f θ - η₁)) *
            Real.exp (-(γ * (t * (inner ℝ (EuclideanSpace.single k σ) a + c)))) := by
          gcongr
      _ = Real.exp (γ * (f (θ + t • EuclideanSpace.single k σ) - f θ + 2 * η₁ -
            t * inner ℝ (EuclideanSpace.single k σ) a - t * c)) := by
          rw [← Real.exp_sub, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(γ * (t * c / 2))) := by
          apply Real.exp_le_exp.2
          rw [real_inner_comm] at hf
          have : f (θ + t • EuclideanSpace.single k σ) - f θ + 2 * η₁ -
              t * inner ℝ (EuclideanSpace.single k σ) a - t * c ≤ -(t * c / 2) := by linarith
          nlinarith
  -- the complement of the ball is covered by the 2d half-spaces
  have hcompl : Uᶜ ⊆ ⋃ k ∈ (Finset.univ : Finset (Fin d)),
      ({x | t * (inner ℝ (EuclideanSpace.single k (1:ℝ)) a + c) ≤
          inner ℝ (t • EuclideanSpace.single k (1:ℝ)) (γ⁻¹ • x)} ∪
       {x | t * (inner ℝ (EuclideanSpace.single k (-1:ℝ)) a + c) ≤
          inner ℝ (t • EuclideanSpace.single k (-1:ℝ)) (γ⁻¹ • x)}) := by
    intro x hx
    simp only [hU_def, Set.mem_compl_iff, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm,
      not_lt] at hx
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or, not_le,
      Finset.mem_univ] at hcon
    have hcoord : ∀ k, |(γ⁻¹ • x - a) k| ≤ c := by
      intro k
      obtain ⟨h1', h2'⟩ := hcon k trivial
      rw [real_inner_smul_left, EuclideanSpace.inner_single_left,
        EuclideanSpace.inner_single_left] at h1' h2'
      simp only [map_one, map_neg, one_mul, neg_mul] at h1' h2'
      have e1 : (γ⁻¹ • x) k < a k + c := by nlinarith
      have e2 : a k - c < (γ⁻¹ • x) k := by nlinarith
      rw [PiLp.sub_apply, abs_le]; constructor <;> linarith
    have hn : ‖γ⁻¹ • x - a‖ ^ 2 < δ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, ((γ⁻¹ • x - a) i) ^ 2 ≤ ∑ _i : Fin d, c ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
        _ = d * c ^ 2 := by simp
        _ < δ ^ 2 := by
            rw [hc_def, div_pow]
            have hd1 : (0:ℝ) < (d + 1) ^ 2 := by positivity
            rw [mul_div_assoc', div_lt_iff₀ hd1]
            have : (d : ℝ) < (d + 1) ^ 2 := by nlinarith
            nlinarith [sq_nonneg δ, mul_pos hδ hδ]
    have := pow_le_pow_left₀ hδ.le hx 2
    linarith
  have hQc : (Q Uᶜ).toReal ≤ 1 / 2 := by
    calc (Q Uᶜ).toReal
        ≤ (∑ k ∈ (Finset.univ : Finset (Fin d)),
            (Q {x | t * (inner ℝ (EuclideanSpace.single k (1:ℝ)) a + c) ≤
                inner ℝ (t • EuclideanSpace.single k (1:ℝ)) (γ⁻¹ • x)} +
             Q {x | t * (inner ℝ (EuclideanSpace.single k (-1:ℝ)) a + c) ≤
                inner ℝ (t • EuclideanSpace.single k (-1:ℝ)) (γ⁻¹ • x)})).toReal := by
          apply ENNReal.toReal_mono
          · exact ENNReal.sum_ne_top.2 fun _ _ =>
              ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩
          · exact (measure_mono hcompl).trans ((measure_biUnion_finset_le _ _).trans
              (Finset.sum_le_sum fun k _ => measure_union_le _ _))
      _ = ∑ k ∈ (Finset.univ : Finset (Fin d)),
            ((Q {x | t * (inner ℝ (EuclideanSpace.single k (1:ℝ)) a + c) ≤
                inner ℝ (t • EuclideanSpace.single k (1:ℝ)) (γ⁻¹ • x)}).toReal +
             (Q {x | t * (inner ℝ (EuclideanSpace.single k (-1:ℝ)) a + c) ≤
                inner ℝ (t • EuclideanSpace.single k (-1:ℝ)) (γ⁻¹ • x)}).toReal) := by
          rw [ENNReal.toReal_sum fun _ _ =>
            ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩]
          exact Finset.sum_congr rfl fun k _ =>
            ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
      _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin d)),
            (Real.exp (-(γ * (t * c / 2))) + Real.exp (-(γ * (t * c / 2)))) :=
          Finset.sum_le_sum fun k _ => add_le_add (hdirQ 1 (by norm_num) k hpos)
            (hdirQ (-1) (by norm_num) k hneg)
      _ = (2 * d : ℝ) * Real.exp (-(γ * (t * c / 2))) := by simp; ring
      _ ≤ 1 / 2 := hsm
  have hQU : 1 / 2 ≤ (Q U).toReal := by
    have h := measure_add_measure_compl (μ := Q) hUm
    rw [measure_univ] at h
    have h' := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h'
    linarith
  -- comparison of the tilted and original laws on the ball
  set E : ℝ := Real.exp (γ * (inner ℝ θ a + ‖θ‖ * δ)) with hE_def
  have hpt : ∀ x ∈ U, ENNReal.ofReal (Real.exp (inner ℝ θ x) /
      ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) ≤
      ENNReal.ofReal (E / ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ hZpos.le
    apply Real.exp_le_exp.2
    simp only [hU_def, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm] at hx
    have hxs : inner ℝ θ x = γ * inner ℝ θ (γ⁻¹ • x) := by
      rw [inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul]
    have h2' : inner ℝ θ (γ⁻¹ • x - a) ≤ ‖θ‖ * ‖γ⁻¹ • x - a‖ := real_inner_le_norm _ _
    have h3' : ‖θ‖ * ‖γ⁻¹ • x - a‖ ≤ ‖θ‖ * δ := mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)
    rw [inner_sub_right] at h2'
    rw [hxs]
    exact mul_le_mul_of_nonneg_left (by linarith) hγ.le
  have hle : Q U ≤ ENNReal.ofReal (E / ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) * ν γ U := by
    rw [hQ_def, tilted_apply' _ _ hUm]
    calc ∫⁻ x in U, ENNReal.ofReal (Real.exp (inner ℝ θ x) / ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ))
          ∂(ν γ)
        ≤ ∫⁻ x in U, ENNReal.ofReal (E / ∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) ∂(ν γ) :=
          setLIntegral_mono measurable_const hpt
      _ = _ := by rw [setLIntegral_const]
  have hle' : (Q U).toReal ≤ E / (∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) * (ν γ U).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hEpos : 0 < E := Real.exp_pos _
  have hfθ : (μ θ).toReal = f θ := rfl
  rw [hfθ]
  have hkey : 1 / 2 * (∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) * E⁻¹ ≤ (ν γ U).toReal := by
    have h2 := hQU.trans hle'
    rw [div_mul_eq_mul_div, le_div_iff₀ hZpos] at h2
    calc 1 / 2 * (∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) * E⁻¹
        ≤ E * (ν γ U).toReal * E⁻¹ := by
          apply mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hEpos.le)
      _ = (ν γ U).toReal := by field_simp
  refine le_trans ?_ hkey
  calc Real.exp (γ * (f θ - inner ℝ θ a - ‖θ‖ * δ - η))
      = Real.exp (-(γ * (3 * η / 4))) * Real.exp (γ * (f θ - η / 4)) * E⁻¹ := by
        rw [hE_def, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ 1 / 2 * Real.exp (γ * (f θ - η₁)) * E⁻¹ := by
        gcongr
    _ ≤ 1 / 2 * (∫ y, Real.exp (inner ℝ θ y) ∂(ν γ)) * E⁻¹ := by gcongr


lemma dom_convex (ν : ℝ → Measure (Rd d)) (μ : Rd d → EReal) (h1 : Assumption1 ν μ) :
    Convex ℝ (dom μ) := by
  intro u hu v hv a b ha hb hab
  rcases ha.eq_or_lt with h0 | ha'
  · subst h0; simp at hab; subst hab; simpa using hv
  rcases hb.eq_or_lt with h0 | hb'
  · subst h0; simp at hab; subst hab; simpa using hu
  have hc := mu_convex ν μ h1 u v hu.ne hv.ne b hb' (by linarith)
  have hab' : 1 - b = a := by linarith
  rw [hab'] at hc
  show μ (a • u + b • v) < ⊤
  refine lt_of_le_of_lt hc ?_
  exact EReal.add_lt_top (coe_mul_ne_top ha' hu.ne) (coe_mul_ne_top hb' hv.ne)

/-- The gradient (tangent-plane) inequality for `μ`. -/
lemma grad_ineq (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (θ : Rd d) (hθ : θ ∈ interior (dom μ))
    (x : Rd d) (hx : μ x ≠ ⊤) :
    (μ θ).toReal + inner ℝ (gradE μ θ) (x - θ) ≤ (μ x).toReal := by
  have hb := (halfspace_bound ν μ h1 θ (gradE μ θ) hθ rfl).1
  have h := le_iSup (fun w => ((inner ℝ w (gradE μ θ) : ℝ) : EReal) - μ w) x
  rw [show (⨆ w, ((inner ℝ w (gradE μ θ) : ℝ) : EReal) - μ w) = rate μ (gradE μ θ) from rfl,
    hb] at h
  have hθt : μ θ ≠ ⊤ := (interior_subset hθ : θ ∈ dom μ).ne
  rw [← EReal.coe_toReal hx (mu_ne_bot ν hν μ h1 x),
    ← EReal.coe_toReal hθt (mu_ne_bot ν hν μ h1 θ), ← EReal.coe_sub, ← EReal.coe_sub,
    EReal.coe_le_coe_iff] at h
  rw [inner_sub_right]
  have e1 := real_inner_comm x (gradE μ θ)
  have e2 := real_inner_comm θ (gradE μ θ)
  linarith

/-- The supremum defining the rate is approached at interior points. -/
lemma approx_sup (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (y : Rd d) (r : ℝ)
    (hr : rate μ y = (r : EReal)) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ ∈ interior (dom μ), r - ε ≤ inner ℝ θ y - (μ θ).toReal := by
  have hlt : ((r - ε / 2 : ℝ) : EReal) < rate μ y := by
    rw [hr, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨θ₁, hθ₁⟩ := lt_iSup_iff.1 hlt
  have hθ₁t : μ θ₁ ≠ ⊤ := by
    intro h; rw [h, EReal.sub_top] at hθ₁; exact absurd hθ₁ (not_lt.2 bot_le)
  set m₁ := (μ θ₁).toReal with hm₁
  have hμ₁ : μ θ₁ = (m₁ : EReal) := (EReal.coe_toReal hθ₁t (mu_ne_bot ν hν μ h1 θ₁)).symm
  rw [hμ₁, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hθ₁
  set v := inner ℝ θ₁ y - m₁ with hv
  set τ : ℝ := min (1 / 2) (ε / (2 * (|v| + 1))) with hτ
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 / 2 := min_le_left _ _
  have hτv : τ * |v| ≤ ε / 2 := by
    have : τ ≤ ε / (2 * (|v| + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [abs_nonneg v]
  set t := 1 - τ
  have hmem : t • θ₁ ∈ interior (dom μ) := by
    have := (dom_convex ν μ h1).combo_interior_closure_mem_interior h1.zero_mem
      (subset_closure (show θ₁ ∈ dom μ from lt_top_iff_ne_top.2 hθ₁t))
      (a := τ) (b := t) hτ0 (by linarith) (by ring)
    simpa using this
  refine ⟨t • θ₁, hmem, ?_⟩
  have hc := mu_convex ν μ h1 0 θ₁ (by rw [mu_zero ν hν μ h1]; exact EReal.zero_ne_top) hθ₁t t
    (by linarith) (by linarith)
  rw [mu_zero ν hν μ h1, mul_zero, zero_add, smul_zero, zero_add, hμ₁, ← EReal.coe_mul] at hc
  have hft : (μ (t • θ₁)).toReal ≤ t * m₁ := by
    have := EReal.toReal_le_toReal hc (mu_ne_bot ν hν μ h1 _) (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  rw [real_inner_smul_left]
  have : t * v ≥ v - τ * |v| := by
    have : t * v = v - τ * v := by ring
    rw [this]; nlinarith [neg_abs_le v, le_abs_self v]
  nlinarith

lemma norm_sq_combo (u v : Rd d) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • u + t • v‖ ^ 2 ≤ (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 := by
  have h1 : ‖(1 - t) • u + t • v‖ ^ 2 =
      (1 - t) ^ 2 * ‖u‖ ^ 2 + 2 * ((1 - t) * t) * inner ℝ u v + t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
    ring
  have h2 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := norm_sub_sq_real u v
  have h3 : 0 ≤ ‖u - v‖ ^ 2 := sq_nonneg _
  rw [h1]
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht1)]

/-- Approximation by exposed points (gradients at interior points), using a Tikhonov
regularisation and steepness. -/
lemma exposed_approx (ν : ℝ → Measure (Rd d)) (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ) (y : Rd d) (r : ℝ)
    (hr : rate μ y = (r : EReal)) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ ∈ interior (dom μ), ‖gradE μ θ - y‖ < ε ∧ rate μ (gradE μ θ) ≤ (r : EReal) := by
  set D := interior (dom μ) with hD_def
  set f : Rd d → ℝ := fun w => (μ w).toReal with hf_def
  have hD0 : (0 : Rd d) ∈ D := h1.zero_mem
  have hDconv : Convex ℝ D := (dom_convex ν μ h1).interior
  have hfin : ∀ w ∈ D, μ w = ((f w : ℝ) : EReal) := fun w hw =>
    (EReal.coe_toReal (interior_subset hw : w ∈ dom μ).ne (mu_ne_bot ν hν μ h1 w)).symm
  have hF5 : ∀ w ∈ D, inner ℝ w y - f w ≤ r := by
    intro w hw
    have h := le_iSup (fun w => ((inner ℝ w y : ℝ) : EReal) - μ w) w
    rw [show (⨆ w, ((inner ℝ w y : ℝ) : EReal) - μ w) = rate μ y from rfl, hr, hfin w hw,
      ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    exact h
  have hfcont : ContinuousOn f D := h1.differentiableOn.continuousOn
  obtain ⟨θh, hθhD, hθh⟩ := approx_sup ν hν μ h1 y r hr (ε ^ 2 / 8) (by positivity)
  set κ : ℝ := min 1 (ε / (2 * (‖θh‖ + 1))) with hκ_def
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκ2 : κ * ‖θh‖ ≤ ε / 2 := by
    have : κ ≤ ε / (2 * (‖θh‖ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [norm_nonneg θh]
  set F : Rd d → ℝ := fun w => f w - inner ℝ w y + κ / 2 * ‖w‖ ^ 2 with hF_def
  have hFlb : ∀ w ∈ D, -r + κ / 2 * ‖w‖ ^ 2 ≤ F w := fun w hw => by
    have := hF5 w hw; simp only [hF_def]; linarith
  have hFcont : ∀ w ∈ D, ContinuousAt F w := by
    intro w hw
    have hf' : ContinuousAt f w := hfcont.continuousAt (isOpen_interior.mem_nhds hw)
    exact (hf'.sub (continuous_id.inner continuous_const).continuousAt).add
      (continuousAt_const.mul ((continuous_norm.pow 2).continuousAt))
  have hbdd : BddBelow (F '' D) := ⟨-r, by
    rintro _ ⟨w, hw, rfl⟩; have := hFlb w hw; nlinarith [sq_nonneg ‖w‖]⟩
  set m := sInf (F '' D) with hm_def
  have hm_le : ∀ w ∈ D, m ≤ F w := fun w hw => csInf_le hbdd ⟨w, hw, rfl⟩
  have hseq : ∀ n : ℕ, ∃ w ∈ D, F w < m + 1 / (n + 1) := fun n => by
    have hpos : (0:ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (Set.Nonempty.image F ⟨0, hD0⟩)
      (show m < m + 1 / (n + 1) by linarith)
    exact ⟨w, hw, hlt⟩
  choose w hwD hwF using hseq
  have hwb : ∀ n, w n ∈ Metric.closedBall (0 : Rd d) (Real.sqrt (2 * (m + 1 + r) / κ)) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    have h1' := hFlb (w n) (hwD n)
    have h2' := hwF n
    have h3' : (1 : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    rw [le_div_iff₀ hκ0]
    nlinarith
  obtain ⟨θs, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hwb
  have hFlim : Tendsto (fun n => F (w (φ n))) atTop (𝓝 m) := by
    have hφt : Tendsto (fun n => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
      have : Tendsto (fun n => ((φ n : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_right _ 1
          (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
      have := this.inv_tendsto_atTop
      refine this.congr fun n => ?_
      simp
    have hup : Tendsto (fun n => m + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 m) := by
      simpa using (tendsto_const_nhds (x := m)).add hφt
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => hm_le _ (hwD _)) (fun n => (hwF (φ n)).le)
  have hθs_cl : θs ∈ closure D :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun n => hwD (φ n))
  -- convexity and the gradient inequality for F
  have hFconv : ∀ u ∈ D, ∀ v ∈ D, ∀ t : ℝ, 0 < t → t < 1 →
      F ((1 - t) • u + t • v) ≤ (1 - t) * F u + t * F v := by
    intro u hu v hv t ht0 ht1
    have hc := mu_convex ν μ h1 u v (hfin u hu ▸ EReal.coe_ne_top _)
      (hfin v hv ▸ EReal.coe_ne_top _) t ht0 ht1
    have hmem : (1 - t) • u + t • v ∈ D :=
      hDconv hu hv (by linarith) ht0.le (by ring)
    rw [hfin _ hmem, hfin u hu, hfin v hv, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at hc
    have hq := norm_sq_combo u v t ht0.le ht1.le
    simp only [hF_def]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    nlinarith
  have hFgrad : ∀ u ∈ D, ∀ v ∈ D,
      F u + inner ℝ (gradE μ u - y + κ • u) (v - u) ≤ F v := by
    intro u hu v hv
    have hg := grad_ineq ν hν μ h1 u hu v (hfin v hv ▸ EReal.coe_ne_top _)
    have hq : ‖u‖ ^ 2 + 2 * inner ℝ u (v - u) ≤ ‖v‖ ^ 2 := by
      have := norm_sub_sq_real v u
      have h0 := sq_nonneg ‖v - u‖
      have hc := real_inner_comm u v
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
      nlinarith
    have hg' : f u + (inner ℝ (gradE μ u) v - inner ℝ (gradE μ u) u) ≤ f v := by
      have := hg; rw [inner_sub_right] at this; exact this
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at hq
    have hq' := mul_le_mul_of_nonneg_left hq (show (0:ℝ) ≤ κ / 2 by positivity)
    simp only [hF_def]
    rw [inner_add_left, inner_sub_left, real_inner_smul_left, inner_sub_right, inner_sub_right,
      inner_sub_right, real_inner_comm y v, real_inner_comm y u, real_inner_self_eq_norm_sq]
    nlinarith
  ------------------------------------------------------------------
  -- the limit point lies in the interior of the domain (steepness)
  have hpath : ∀ t : ℝ, 0 ≤ t → t < 1 → t • θs ∈ D := fun t ht0 ht1 => by
    have := (dom_convex ν μ h1).combo_interior_closure_mem_interior hD0
      (closure_mono interior_subset hθs_cl) (a := 1 - t) (b := t) (by linarith) ht0 (by ring)
    simpa using this
  have hθsD : θs ∈ D := by
    by_contra hnot
    have hfr : θs ∈ frontier D := ⟨hθs_cl, by rwa [isOpen_interior.interior_eq]⟩
    have hsteep := h1.steep θs hfr
    -- Claim A
    have hA : ∀ t : ℝ, 0 < t → t < 1 → F (t • θs) ≤ (1 - t) * F 0 + t * m := by
      intro t ht0 ht1
      have h_n : ∀ n, F ((1 - t) • (0 : Rd d) + t • w (φ n)) ≤ (1 - t) * F 0 + t * F (w (φ n)) :=
        fun n => hFconv 0 hD0 _ (hwD _) t ht0 ht1
      have hl0 : Tendsto (fun n => (1 - t) • (0 : Rd d) + t • w (φ n)) atTop (𝓝 (t • θs)) := by
        have := (hlim.const_smul t).const_add ((1 - t) • (0 : Rd d))
        simpa using this
      have hl1 : Tendsto (fun n => F ((1 - t) • (0 : Rd d) + t • w (φ n))) atTop
          (𝓝 (F (t • θs))) :=
        (hFcont _ (hpath t ht0.le ht1)).tendsto.comp hl0
      have hl2 : Tendsto (fun n => (1 - t) * F 0 + t * F (w (φ n))) atTop
          (𝓝 ((1 - t) * F 0 + t * m)) :=
        tendsto_const_nhds.add (hFlim.const_mul t)
      exact le_of_tendsto_of_tendsto' hl1 hl2 h_n
    -- Claim B
    have hB : ∀ t : ℝ, 0 < t → t < 1 →
        inner ℝ (gradE μ (t • θs) - y + κ • (t • θs)) θs ≤ 0 := by
      intro t ht0 ht1
      set P := inner ℝ (gradE μ (t • θs) - y + κ • (t • θs)) θs with hP
      have hs : ∀ s : ℝ, t < s → s < 1 → (s - t) * P ≤ (1 - s) * (F 0 - m) := by
        intro s hts hs1
        have g := hFgrad (t • θs) (hpath t ht0.le ht1) (s • θs) (hpath s (by linarith) hs1)
        rw [← sub_smul, real_inner_smul_right] at g
        have hAs := hA s (by linarith) hs1
        have hmt := hm_le (t • θs) (hpath t ht0.le ht1)
        nlinarith
      by_contra hpos
      push Not at hpos
      set C := |F 0 - m| + 1 with hC
      have hC0 : 0 < C := by positivity
      set e := min ((1 - t) / 2) ((1 - t) * P / (4 * C)) with he
      have he0 : 0 < e := lt_min (by linarith) (by
        have : 0 < (1 - t) * P := mul_pos (by linarith) hpos
        positivity)
      have he1 : e ≤ (1 - t) / 2 := min_le_left _ _
      have he2 : e ≤ (1 - t) * P / (4 * C) := min_le_right _ _
      have h := hs (1 - e) (by linarith) (by linarith)
      have h3 : (1 - (1 - e)) * (F 0 - m) ≤ e * C := by
        have := le_abs_self (F 0 - m)
        nlinarith
      have h4 : e * C ≤ (1 - t) * P / 4 := by
        rw [le_div_iff₀ (by positivity)] at he2
        nlinarith
      have h5 : (1 - t) / 2 * P ≤ (1 - e - t) * P := by
        apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
      nlinarith
    -- Claim C: a uniform bound on the gradients along the path
    obtain ⟨ρ, hρ, hballρ⟩ := Metric.isOpen_iff.1 isOpen_interior 0 hD0
    have hcb : Metric.closedBall (0 : Rd d) (ρ / 2) ⊆ D := fun z hz =>
      hballρ (Metric.closedBall_subset_ball (by linarith) hz)
    obtain ⟨K, hK⟩ : ∃ K, ∀ z ∈ Metric.closedBall (0 : Rd d) (ρ / 2), f z ≤ K := by
      obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Rd d) (ρ / 2)).bddAbove_image
        (hfcont.mono hcb)
      exact ⟨K, fun z hz => hK ⟨z, hz, rfl⟩⟩
    have hCb : ∀ t : ℝ, 0 < t → t < 1 →
        ρ / 2 * ‖gradE μ (t • θs)‖ ≤ K + 2 * (‖y‖ * ‖θs‖) + |r| := by
      intro t ht0 ht1
      set g := gradE μ (t • θs) with hg
      have hmem := hpath t ht0.le ht1
      have hlow : -(‖y‖ * ‖θs‖) - |r| ≤ f (t • θs) := by
        have := hF5 _ hmem
        have h2 : |inner ℝ (t • θs) y| ≤ ‖t • θs‖ * ‖y‖ := abs_real_inner_le_norm _ _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at h2
        have h3 : t * ‖θs‖ * ‖y‖ ≤ ‖θs‖ * ‖y‖ := by
          have := mul_nonneg (norm_nonneg θs) (norm_nonneg y)
          nlinarith
        have := neg_abs_le (inner ℝ (t • θs) y)
        have := le_abs_self r
        nlinarith
      have hgθ : t * inner ℝ g θs ≤ ‖y‖ * ‖θs‖ := by
        have hb := hB t ht0 ht1
        rw [inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq] at hb
        have hy : inner ℝ y θs ≤ ‖y‖ * ‖θs‖ := real_inner_le_norm _ _
        have hk : 0 ≤ κ * (t * ‖θs‖ ^ 2) := by positivity
        rcases le_or_gt (inner ℝ g θs) 0 with hneg | hpos
        · have := mul_nonneg (norm_nonneg y) (norm_nonneg θs)
          nlinarith
        · nlinarith
      rcases eq_or_ne g 0 with hg0 | hg0
      · rw [hg0, norm_zero, mul_zero]
        have : f 0 ≤ K := hK 0 (Metric.mem_closedBall_self (by linarith))
        have h0 := hF5 0 hD0
        simp only [inner_zero_left] at h0
        have := mul_nonneg (norm_nonneg y) (norm_nonneg θs)
        have := le_abs_self r
        linarith
      set z : Rd d := (ρ / 2 / ‖g‖) • g with hz
      have hgn : 0 < ‖g‖ := norm_pos_iff.2 hg0
      have hzmem : z ∈ Metric.closedBall (0 : Rd d) (ρ / 2) := by
        rw [Metric.mem_closedBall, dist_zero_right, hz, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity), div_mul_cancel₀ _ hgn.ne']
      have hgi := grad_ineq ν hν μ h1 (t • θs) hmem z (hfin z (hcb hzmem) ▸ EReal.coe_ne_top _)
      have hgz : inner ℝ g z = ρ / 2 * ‖g‖ := by
        rw [hz, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      change f (t • θs) + inner ℝ g (z - t • θs) ≤ f z at hgi
      rw [inner_sub_right, hgz, real_inner_smul_right] at hgi
      have := hK z hzmem
      linarith
    -- contradiction with steepness
    set Cb : ℝ := (K + 2 * (‖y‖ * ‖θs‖) + |r|) / (ρ / 2) with hCb_def
    have hev := hsteep.eventually_gt_atTop Cb
    have hpathT : Tendsto (fun t : ℝ => t • θs) (𝓝[<] 1) (𝓝[D] θs) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => t • θs) (𝓝 1) (𝓝 ((1:ℝ) • θs)) :=
          (continuous_id.smul continuous_const).tendsto 1
        rw [one_smul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with t ht
        exact hpath t ht.1.le ht.2
    obtain ⟨t, ht1, ht2⟩ := ((hpathT.eventually hev).and
      (Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num))).exists
    have := hCb t ht2.1 ht2.2
    rw [hCb_def, div_lt_iff₀ (by positivity)] at ht1
    linarith
  ------------------------------------------------------------------
  -- θs minimises F, hence its gradient vanishes
  have hFθs : F θs = m :=
    tendsto_nhds_unique ((hFcont θs hθsD).tendsto.comp hlim) hFlim
  set v := gradE μ θs - y + κ • θs with hv_def
  have hvz : v = 0 := by
    have hfd : HasFDerivAt f (InnerProductSpace.toDual ℝ (Rd d) (gradE μ θs)) θs :=
      (h1.differentiableOn.differentiableAt (isOpen_interior.mem_nhds hθsD)).hasGradientAt.hasFDerivAt
    set g : ℝ → ℝ := fun t => F (θs + t • v) with hg_def
    have hgd : HasDerivAt g (inner ℝ (gradE μ θs) v - inner ℝ v y +
        κ / 2 * (2 * inner ℝ θs v)) 0 := by
      have hl : HasDerivAt (fun t : ℝ => θs + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add θs
      have hs0 : θs + (0:ℝ) • v = θs := by simp
      have hfd' : HasFDerivAt f (InnerProductSpace.toDual ℝ (Rd d) (gradE μ θs))
          (θs + (0:ℝ) • v) := by rw [hs0]; exact hfd
      have h1' := hfd'.comp_hasDerivAt (0:ℝ) hl
      simp only [InnerProductSpace.toDual_apply_apply] at h1'
      have h2' : HasDerivAt (fun t : ℝ => inner ℝ (θs + t • v) y) (inner ℝ v y) 0 := by
        have : (fun t : ℝ => inner ℝ (θs + t • v) y) = fun t => inner ℝ θs y + t * inner ℝ v y := by
          funext t; rw [inner_add_left, real_inner_smul_left]
        rw [this]
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ v y)).const_add (inner ℝ θs y)
      have h3' : HasDerivAt (fun t : ℝ => ‖θs + t • v‖ ^ 2) (2 * inner ℝ θs v) 0 := by
        have : (fun t : ℝ => ‖θs + t • v‖ ^ 2) =
            fun t => ‖θs‖ ^ 2 + t * (2 * inner ℝ θs v) + t ^ 2 * ‖v‖ ^ 2 := by
          funext t
          rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
            sq_abs]
          ring
        rw [this]
        have := (((hasDerivAt_id (0:ℝ)).mul_const (2 * inner ℝ θs v)).const_add (‖θs‖ ^ 2)).add
          ((hasDerivAt_pow 2 (0:ℝ)).mul_const (‖v‖ ^ 2))
        exact this.congr_deriv (by simp)
      have := (h1'.sub h2').add (h3'.const_mul (κ / 2))
      exact this
    have hmin : IsLocalMin g 0 := by
      have hcont : Continuous fun t : ℝ => θs + t • v := continuous_const.add
        (continuous_id.smul continuous_const)
      have hloc : IsLocalMin F θs := by
        filter_upwards [isOpen_interior.mem_nhds hθsD] with w hw
        rw [hFθs]; exact hm_le w hw
      have hloc' : IsLocalMin F (θs + (0:ℝ) • v) := by rw [zero_smul, add_zero]; exact hloc
      exact IsLocalMin.comp_continuous (g := fun t : ℝ => θs + t • v) (b := 0) hloc'
        hcont.continuousAt
    have h0 := hmin.hasDerivAt_eq_zero hgd
    have e : inner ℝ v v = inner ℝ (gradE μ θs) v - inner ℝ v y +
        κ / 2 * (2 * inner ℝ θs v) := by
      show inner ℝ (gradE μ θs - y + κ • θs) v = _
      rw [inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_comm y v]
      ring
    have : inner ℝ v v = 0 := by rw [e]; exact h0
    exact inner_self_eq_zero.1 this
  have hgrad : gradE μ θs = y - κ • θs := by
    have := hvz; rw [hv_def] at this
    rw [← sub_eq_zero]; rw [← this]; abel
  refine ⟨θs, hθsD, ?_, ?_⟩
  · -- the gradient is close to y
    rw [hgrad, show y - κ • θs - y = -(κ • θs) by abel, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hκ0]
    have hθhF : F θh ≤ -r + ε ^ 2 / 8 + κ / 2 * ‖θh‖ ^ 2 := by
      have e : F θh = f θh - inner ℝ θh y + κ / 2 * ‖θh‖ ^ 2 := rfl
      have e2 : f θh = (μ θh).toReal := rfl
      rw [e, e2]; linarith
    have hmθ : F θs ≤ F θh := by rw [hFθs]; exact hm_le θh hθhD
    have hlow := hFlb θs hθsD
    have h2 : κ / 2 * ‖θs‖ ^ 2 ≤ ε ^ 2 / 8 + κ / 2 * ‖θh‖ ^ 2 := by linarith
    have h3 : (κ * ‖θs‖) ^ 2 < ε ^ 2 := by
      have h4 : (κ * ‖θs‖) ^ 2 ≤ κ * (ε ^ 2 / 4) + (κ * ‖θh‖) ^ 2 := by
        calc (κ * ‖θs‖) ^ 2 = 2 * κ * (κ / 2 * ‖θs‖ ^ 2) := by ring
          _ ≤ 2 * κ * (ε ^ 2 / 8 + κ / 2 * ‖θh‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = κ * (ε ^ 2 / 4) + (κ * ‖θh‖) ^ 2 := by ring
      have h5 : (κ * ‖θh‖) ^ 2 ≤ (ε / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hκ2 2
      have h6 : κ * (ε ^ 2 / 4) ≤ ε ^ 2 / 4 :=
        mul_le_of_le_one_left (by positivity) hκ1
      have h7 : 0 < ε ^ 2 := by positivity
      linarith
    exact abs_lt_of_sq_lt_sq' h3 hε.le |>.2
  · -- the rate at the exposed point
    have hb := (halfspace_bound ν μ h1 θs (gradE μ θs) hθsD rfl).1
    rw [hb, hfin θs hθsD, ← EReal.coe_sub, EReal.coe_le_coe_iff, hgrad, inner_sub_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    have := hF5 θs hθsD
    have : 0 ≤ κ * ‖θs‖ ^ 2 := by positivity
    linarith

end ProbEffIS.GE.LB

open ProbEffIS.GE ProbEffIS.GE.LB in
theorem solution {d : ℕ} (ν : ℝ → Measure (Rd d))
    (hν : ∀ᶠ γ in atTop, IsProbabilityMeasure (ν γ))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (B : Set (Rd d)) (hB : MeasurableSet B) :
    -(rateOn μ (interior B)) ≤
      liminf (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
        ENNReal.log (ν γ {x | γ⁻¹ • x ∈ B})) atTop := by
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hI : rateOn μ (interior B) < ((-z : ℝ) : EReal) := by
    rw [EReal.coe_neg]; exact EReal.lt_neg_comm.1 hz
  obtain ⟨y, hy'⟩ := iInf_lt_iff.1 hI
  obtain ⟨hyB, hy⟩ := iInf_lt_iff.1 hy'
  have hy0 : 0 ≤ rate μ y := by
    have := le_iSup (fun x => ((inner ℝ x y : ℝ) : EReal) - μ x) 0
    simp only [mu_zero ν hν μ h1, inner_zero_left, EReal.coe_zero, sub_zero] at this
    exact this
  have hytop : rate μ y ≠ ⊤ := (lt_of_lt_of_le hy le_top).ne
  set r := (rate μ y).toReal with hr_def
  have hr : rate μ y = (r : EReal) := (EReal.coe_toReal hytop (ne_bot_of_le_ne_bot
    EReal.zero_ne_bot hy0)).symm
  have hrz : r < -z := by rw [hr, EReal.coe_lt_coe_iff] at hy; exact hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hyB
  set η : ℝ := (-z - r) / 2 with hη_def
  have hη : 0 < η := by rw [hη_def]; linarith
  obtain ⟨θ, hθD, hθy, hθr⟩ := exposed_approx ν hν μ h1 y r hr (ε / 2) (by positivity)
  set a := gradE μ θ with ha_def
  have hb := (halfspace_bound ν μ h1 θ a hθD rfl).1
  have hθfin : μ θ = ((μ θ).toReal : EReal) :=
    (EReal.coe_toReal (interior_subset hθD : θ ∈ dom μ).ne (mu_ne_bot ν hν μ h1 θ)).symm
  have hra : inner ℝ θ a - (μ θ).toReal ≤ r := by
    rw [hb, hθfin, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hθr; exact hθr
  set δ : ℝ := min (ε / 2) (η / (2 * (‖θ‖ + 1))) with hδ_def
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : ‖θ‖ * δ ≤ η / 2 := by
    have : δ ≤ η / (2 * (‖θ‖ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [norm_nonneg θ]
  have hsub : Metric.ball a δ ⊆ B := by
    intro x hx
    apply interior_subset
    apply hball
    rw [Metric.mem_ball] at hx ⊢
    have := dist_triangle x a y
    rw [dist_eq_norm a y] at this
    linarith
  have hll := tilt_llb ν hν μ h1 θ hθD δ hδ0 (η / 2) (by positivity)
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hll, hν, eventually_gt_atTop (0:ℝ)] with γ hγ hP hγ0
  have hmono : (ν γ {x | γ⁻¹ • x ∈ Metric.ball a δ}).toReal ≤ (ν γ {x | γ⁻¹ • x ∈ B}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun x hx => hsub hx)
  have hlow : Real.exp (γ * z) ≤ (ν γ {x | γ⁻¹ • x ∈ B}).toReal := by
    refine le_trans ?_ (hγ.trans hmono)
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hγ0.le
    rw [← ha_def]
    linarith
  have hpos : 0 < (ν γ {x | γ⁻¹ • x ∈ B}).toReal := lt_of_lt_of_le (Real.exp_pos _) hlow
  have hne : ν γ {x | γ⁻¹ • x ∈ B} ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hne, ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_mul,
    EReal.coe_le_coe_iff]
  have hl : γ * z ≤ Real.log (ν γ {x | γ⁻¹ • x ∈ B}).toReal := by
    have := Real.log_le_log (Real.exp_pos _) hlow
    rwa [Real.log_exp] at this
  rw [le_inv_mul_iff₀ hγ0]
  linarith

