-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P30.exponentialRepresentation_continuous_trivialSmoothVectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:51:27.839347+00:00
-- url     : https://prove2.me/submissions/d6d227e7-d2ad-4373-b1b5-c22e8d318948

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P30
noncomputable section

open MeasureTheory Filter Topology Metric

open QAlgorithms.Papers.Independent.Next46.P30

open scoped ENNReal

lemma g61b_norm_of_ae (u : HilbertSpace) (F : ℝ → ℂ) (h : (u : ℝ → ℂ) =ᵐ[intervalMeasure] F) :
    ‖u‖ = (eLpNorm F 2 intervalMeasure).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae h]

lemma g61b_sub_ae (f g : GroupSpace) (xi eta : HilbertSpace) :
    ((phaseAction f xi - phaseAction g eta : HilbertSpace) : ℝ → ℂ) =ᵐ[intervalMeasure]
      fun t => phaseProduct f xi t - phaseProduct g eta t := by
  filter_upwards [Lp.coeFn_sub (phaseAction f xi) (phaseAction g eta),
    (MemLp.coeFn_toLp _ : (phaseAction f xi : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct f xi),
    (MemLp.coeFn_toLp _ : (phaseAction g eta : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct g eta)]
    with t h1 h2 h3
  rw [h1, Pi.sub_apply]
  exact congrArg₂ (· - ·) h2 h3

lemma g61b_isometry (f : GroupSpace) (xi eta : HilbertSpace) :
    ‖phaseAction f xi - phaseAction f eta‖ = ‖xi - eta‖ := by
  rw [g61b_norm_of_ae _ _ (g61b_sub_ae f f xi eta), Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [Lp.coeFn_sub xi eta] with t ht
  rw [ht, Pi.sub_apply]
  simp only [phaseProduct, ← mul_sub, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

lemma g61b_exp_diff (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  simpa [Real.norm_eq_abs] using this

lemma g61b_pointwise (a b : ℝ) (z : ℂ) (M : ℝ) (hM : 0 < M) :
    ‖(Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))) * z‖ ≤
      2 * ‖({w : ℂ | M ≤ ‖w‖₊}.indicator id z)‖ + M * ‖a - b‖ := by
  rw [norm_mul]
  by_cases hz : M ≤ ‖z‖₊
  · rw [Set.indicator_of_mem (show z ∈ {w : ℂ | M ≤ ‖w‖₊} from hz), id]
    have h1 : ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ 2 := by
      calc _ ≤ ‖Complex.exp (Complex.I * (a : ℂ))‖ + ‖Complex.exp (Complex.I * (b : ℂ))‖ :=
            norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]; norm_num
    have : 0 ≤ M * ‖a - b‖ := by positivity
    nlinarith [norm_nonneg z]
  · rw [Set.indicator_of_notMem (show z ∉ {w : ℂ | M ≤ ‖w‖₊} from hz)]
    have hz' : ‖z‖ ≤ M := by
      have : (‖z‖₊ : ℝ) < M := lt_of_not_ge hz
      exact this.le
    have h1 := g61b_exp_diff a b
    rw [norm_zero, mul_zero, zero_add, Real.norm_eq_abs]
    calc _ ≤ |a - b| * M := mul_le_mul h1 hz' (norm_nonneg _) (abs_nonneg _)
      _ = M * |a - b| := mul_comm _ _

lemma g61b_unif (eta : HilbertSpace) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ f g : GroupSpace,
      ‖phaseAction f eta - phaseAction g eta‖ ≤ ε + M * ‖f - g‖ := by
  obtain ⟨M, hM, hI⟩ := (Lp.memLp eta).eLpNorm_indicator_norm_ge_pos_le
    (Lp.stronglyMeasurable eta) (ε := ε / 2) (by positivity)
  refine ⟨M, hM, fun f g => ?_⟩
  set I : ℝ → ℂ := {x | M ≤ ‖(eta : ℝ → ℂ) x‖₊}.indicator (eta : ℝ → ℂ) with hIdef
  have hIfin : eLpNorm I 2 intervalMeasure < ∞ := lt_of_le_of_lt hI ENNReal.ofReal_lt_top
  have hIm : AEStronglyMeasurable I intervalMeasure :=
    (Lp.aestronglyMeasurable eta).indicator
      (measurableSet_le measurable_const (Lp.stronglyMeasurable eta).measurable.nnnorm.coe_nnreal_real)
  have hfg : AEStronglyMeasurable (fun t => (f : ℝ → ℝ) t - (g : ℝ → ℝ) t) intervalMeasure :=
    (Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g)
  have hfgn : eLpNorm (fun t => (f : ℝ → ℝ) t - (g : ℝ → ℝ) t) 2 intervalMeasure =
      eLpNorm (⇑(f - g)) 2 intervalMeasure := by
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with t ht
    rw [ht, Pi.sub_apply]
  have hfgfin : eLpNorm (⇑(f - g)) 2 intervalMeasure < ∞ := Lp.eLpNorm_lt_top _
  rw [g61b_norm_of_ae _ _ (g61b_sub_ae f g eta eta)]
  have hbound : eLpNorm (fun t => phaseProduct f eta t - phaseProduct g eta t) 2 intervalMeasure ≤
      eLpNorm (fun t => 2 * ‖I t‖ + M * ‖(f : ℝ → ℝ) t - (g : ℝ → ℝ) t‖) 2 intervalMeasure := by
    apply eLpNorm_mono_real
    intro t
    have := g61b_pointwise ((f : ℝ → ℝ) t) ((g : ℝ → ℝ) t) ((eta : ℝ → ℂ) t) M hM
    simp only [phaseProduct, ← sub_mul]
    convert this using 3
    simp only [hIdef, Set.indicator, id, coe_nnnorm, Set.mem_setOf_eq]
  have hsum : eLpNorm (fun t => 2 * ‖I t‖ + M * ‖(f : ℝ → ℝ) t - (g : ℝ → ℝ) t‖) 2
      intervalMeasure ≤ ENNReal.ofReal 2 * eLpNorm I 2 intervalMeasure +
        ENNReal.ofReal M * eLpNorm (⇑(f - g)) 2 intervalMeasure := by
    refine (eLpNorm_add_le ?_ ?_ (by norm_num)).trans ?_
    · exact (hIm.norm.const_mul 2)
    · exact (hfg.norm.const_mul M)
    gcongr
    · rw [show (fun t => 2 * ‖I t‖) = (2 : ℝ) • (fun t => ‖I t‖) from rfl, eLpNorm_const_smul,
        eLpNorm_norm]
      simp [Real.enorm_eq_ofReal]
    · rw [show (fun t => M * ‖(f : ℝ → ℝ) t - (g : ℝ → ℝ) t‖) =
          M • (fun t => ‖(f : ℝ → ℝ) t - (g : ℝ → ℝ) t‖) from rfl, eLpNorm_const_smul,
        eLpNorm_norm, hfgn]
      simp [Real.enorm_eq_ofReal hM.le]
  have htot := hbound.trans hsum
  have hfinR : ENNReal.ofReal 2 * eLpNorm I 2 intervalMeasure +
      ENNReal.ofReal M * eLpNorm (⇑(f - g)) 2 intervalMeasure ≠ ∞ := by
    apply ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfgfin.ne
  calc _ ≤ (ENNReal.ofReal 2 * eLpNorm I 2 intervalMeasure +
        ENNReal.ofReal M * eLpNorm (⇑(f - g)) 2 intervalMeasure).toReal :=
        ENNReal.toReal_mono hfinR htot
    _ = 2 * (eLpNorm I 2 intervalMeasure).toReal + M * ‖f - g‖ := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfgfin.ne), ENNReal.toReal_mul,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal hM.le,
          Lp.norm_def]
    _ ≤ ε + M * ‖f - g‖ := by
        have : (eLpNorm I 2 intervalMeasure).toReal ≤ ε / 2 := by
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hI
          rwa [ENNReal.toReal_ofReal (by positivity)] at this
        linarith

theorem g61b_cont :
    Continuous (fun z : GroupSpace × HilbertSpace => phaseAction z.1 z.2) := by
  rw [Metric.continuous_iff]
  rintro ⟨f0, xi0⟩ ε hε
  obtain ⟨M, hM, hU⟩ := g61b_unif xi0 (ε / 4) (by positivity)
  refine ⟨min (ε / 4) (ε / (4 * M)), by positivity, ?_⟩
  rintro ⟨f, xi⟩ hd
  have hd1 : dist f f0 < min (ε / 4) (ε / (4 * M)) := lt_of_le_of_lt (le_max_left _ _) hd
  have hd2 : dist xi xi0 < min (ε / 4) (ε / (4 * M)) := lt_of_le_of_lt (le_max_right _ _) hd
  rw [dist_eq_norm] at hd1 hd2 ⊢
  have e1 := g61b_isometry f xi xi0
  have e2 := hU f f0
  have hm1 : ‖f - f0‖ < ε / (4 * M) := lt_of_lt_of_le hd1 (min_le_right _ _)
  have hm2 : ‖xi - xi0‖ < ε / 4 := lt_of_lt_of_le hd2 (min_le_left _ _)
  have hMf : M * ‖f - f0‖ ≤ ε / 4 := by
    have := mul_lt_mul_of_pos_left hm1 hM
    rw [show M * (ε / (4 * M)) = ε / 4 by field_simp] at this
    exact this.le
  calc ‖phaseAction f xi - phaseAction f0 xi0‖
      ≤ ‖phaseAction f xi - phaseAction f xi0‖ + ‖phaseAction f xi0 - phaseAction f0 xi0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

lemma g61b_leb {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hfin : ∫⁻ y, f y ≠ ∞) :
    ∀ᵐ x : ℝ, Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, f y) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_lintegral_div
    hf.aemeasurable hfin] with x hx
  refine hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (volume : Measure ℝ)
    (fun _ => x) (fun r => r) tendsto_id ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [one_mul, mem_closedBall, dist_self]
  exact le_of_lt hr

lemma g61b_second {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : E → F) (hΦ : ContDiff ℝ 2 Φ) :
    ∃ K ρ : ℝ, 0 ≤ K ∧ 0 < ρ ∧ ∀ h : E, ‖h‖ < ρ →
      ‖Φ h + Φ (-h) - (2 : ℝ) • Φ 0‖ ≤ K * ‖h‖ ^ 2 := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have h1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ Φ) := h1.differentiable one_ne_zero
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ Φ)) := h1.continuous_fderiv one_ne_zero
  have hc3 : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ Φ) x‖) := by
    have := (continuous_norm (E := E →L[ℝ] E →L[ℝ] F))
    exact this.comp hc2
  obtain ⟨ρ, hρ, hρb⟩ := Metric.continuous_iff.1 hc3 (0 : E) 1 one_pos
  set K0 := ‖fderiv ℝ (fderiv ℝ Φ) 0‖ + 1
  have hK0 : 0 ≤ K0 := by positivity
  have hD2 : ∀ x ∈ ball (0 : E) ρ, ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ K0 := by
    intro x hx
    have := hρb x (by simpa using hx)
    rw [Real.dist_eq, abs_lt] at this
    linarith
  have hD1 : ∀ x : E, ‖x‖ < ρ → ‖fderiv ℝ Φ x - fderiv ℝ Φ (-x)‖ ≤ K0 * (2 * ‖x‖) := by
    intro x hx
    have := (convex_ball (0 : E) ρ).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hd1 y) hD2 (y := x) (x := -x) (by simpa using hx) (by simpa using hx)
    rwa [sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_two] at this
  refine ⟨2 * K0, ρ, by positivity, hρ, fun h hh => ?_⟩
  let φ : E → F := fun x => Φ x + Φ (-x)
  let φ' : E → E →L[ℝ] F := fun x => fderiv ℝ Φ x - fderiv ℝ Φ (-x)
  have hφ : ∀ x, HasFDerivAt φ (φ' x) x := by
    intro x
    have := (hd x).hasFDerivAt.add (((hd (-x)).hasFDerivAt).comp x ((hasFDerivAt_id (𝕜 := ℝ) x).neg))
    refine this.congr_fderiv ?_
    ext v; simp [φ', sub_eq_add_neg]
  have hb : ∀ x ∈ closedBall (0 : E) ‖h‖, ‖φ' x‖ ≤ 2 * K0 * ‖h‖ := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    calc ‖φ' x‖ ≤ K0 * (2 * ‖x‖) := hD1 x (lt_of_le_of_lt hx hh)
      _ ≤ 2 * K0 * ‖h‖ := by nlinarith
  have := (convex_closedBall (0 : E) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hφ x).hasFDerivWithinAt) hb (y := h) (x := 0)
    (by simp) (by simp)
  simp only [φ, neg_zero, sub_zero] at this
  rw [two_smul]
  calc _ ≤ 2 * K0 * ‖h‖ * ‖h‖ := this
    _ = 2 * K0 * ‖h‖ ^ 2 := by ring

lemma g61b_zero_of_small (xi : HilbertSpace) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫⁻ y in closedBall lam r, (Set.Icc (0 : ℝ) 1).indicator
        (fun t => ENNReal.ofReal (‖xi t‖ ^ 2)) y ≤ ENNReal.ofReal (K * r ^ 2)) :
    xi = 0 := by
  set S := Set.Icc (0 : ℝ) 1 with hS
  have hSm : MeasurableSet S := measurableSet_Icc
  let f : ℝ → ℝ≥0∞ := S.indicator (fun t => ENNReal.ofReal (‖xi t‖ ^ 2))
  have hxm : Measurable (fun t => ENNReal.ofReal (‖xi t‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((Lp.stronglyMeasurable xi).measurable.norm.pow_const 2)
  have hfm : Measurable f := hxm.indicator hSm
  have hint : Integrable (fun t => ‖xi t‖ ^ 2) intervalMeasure :=
    (Lp.memLp xi).integrable_norm_pow (by norm_num)
  have hfin : ∫⁻ y, f y ≠ ∞ := by
    rw [lintegral_indicator hSm]
    exact (hint.lintegral_lt_top).ne
  have hae := g61b_leb hfm hfin
  have h0 : ∀ᵐ t ∂intervalMeasure, xi t = 0 := by
    rw [ae_iff]
    change (volume.restrict S) {a | ¬ xi a = 0} = 0
    rw [Measure.restrict_apply' hSm]
    by_contra hne
    have hex : ∃ lam, (lam ∈ {a | ¬ xi a = 0} ∩ S) ∧
        Tendsto (fun r : ℝ => (∫⁻ y in closedBall lam r, f y) / volume (closedBall lam r))
          (𝓝[>] 0) (𝓝 (f lam)) := by
      by_contra hno
      push Not at hno
      apply hne
      apply measure_mono_null _ (ae_iff.1 hae)
      intro a ha hc
      exact hno a ha hc
    obtain ⟨lam, ⟨hxl, hlS⟩, hlim⟩ := hex
    have hc : f lam = ENNReal.ofReal (‖xi lam‖ ^ 2) := Set.indicator_of_mem hlS _
    have hcpos : f lam ≠ 0 := by
      rw [hc]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : xi lam ≠ 0 := hxl
      positivity
    have hcfin : f lam ≠ ∞ := by rw [hc]; exact ENNReal.ofReal_ne_top
    set c := f lam
    have hev1 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        c / 2 < (∫⁻ y in closedBall lam r, f y) / volume (closedBall lam r) :=
      hlim (Ioi_mem_nhds (ENNReal.half_lt_self hcpos hcfin))
    have htend : Tendsto (fun r : ℝ => ENNReal.ofReal (K * r)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => K * r) (𝓝[>] 0) (𝓝 (K * 0)) :=
        ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [mul_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (K * r) < c :=
      htend (Iio_mem_nhds (pos_iff_ne_zero.2 hcpos))
    obtain ⟨r, ⟨⟨h1, h2⟩, h3⟩, hr⟩ :=
      (((hev1.and hev2).and (hK lam hlS)).and self_mem_nhdsWithin).exists
    have hr : (0 : ℝ) < r := hr
    rw [Real.volume_closedBall] at h1
    have h1' : c / 2 * ENNReal.ofReal (2 * r) < ∫⁻ y in closedBall lam r, f y := by
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by simp; positivity)) (Or.inl ENNReal.ofReal_ne_top)]
        at h1
      exact h1
    have e1 : c / 2 * ENNReal.ofReal (2 * r) = c * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul (by norm_num), ← mul_assoc, ENNReal.ofReal_ofNat,
        ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    have e2 : ENNReal.ofReal (K * r ^ 2) = ENNReal.ofReal (K * r) * ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
    have := lt_of_lt_of_le h1' h3
    rw [e1, e2, ENNReal.mul_lt_mul_iff_left (by simp; positivity) ENNReal.ofReal_ne_top] at this
    exact absurd h2 (not_lt.2 this.le)
  apply Lp.ext
  filter_upwards [h0, Lp.coeFn_zero ℂ 2 intervalMeasure] with t ht hz
  rw [ht, hz]; rfl

lemma g61b_phase_zero (xi : HilbertSpace) : phaseAction 0 xi = xi := by
  apply Lp.ext
  have ha : (phaseAction 0 xi : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct 0 xi :=
    MemLp.coeFn_toLp _
  filter_upwards [ha, Lp.coeFn_zero ℝ 2 intervalMeasure] with t ht hzero
  change (0 : GroupSpace) t = 0 at hzero
  change (phaseAction 0 xi) t =
    Complex.exp (Complex.I * ((0 : GroupSpace) t : ℂ)) * xi t at ht
  rw [hzero] at ht
  simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using ht

lemma g61b_act_zero (f : GroupSpace) : phaseAction f (0 : HilbertSpace) = 0 := by
  apply Lp.ext
  have ha : (phaseAction f 0 : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct f 0 :=
    MemLp.coeFn_toLp _
  filter_upwards [ha, Lp.coeFn_zero ℂ 2 intervalMeasure] with t ht hzero
  rw [ht, hzero, phaseProduct, hzero]; simp

lemma g61b_ball (xi : HilbertSpace) (K ρ : ℝ) (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hb : ∀ h : GroupSpace, ‖h‖ < ρ →
      ‖phaseAction h xi + phaseAction (-h) xi - (2 : ℝ) • phaseAction 0 xi‖ ≤ K * ‖h‖ ^ 2)
    (lam r : ℝ) (hr : 0 < r) (hsmall : Real.pi ^ 2 * (2 * r) < ρ ^ 2) :
    ∫⁻ y in closedBall lam r, (Set.Icc (0 : ℝ) 1).indicator
        (fun t => ENNReal.ofReal (‖xi t‖ ^ 2)) y ≤
      ENNReal.ofReal ((K ^ 2 * Real.pi ^ 4) * r ^ 2) := by
  set I := Set.Icc (0 : ℝ) 1 with hIdef
  have hI : MeasurableSet I := measurableSet_Icc
  set B := closedBall lam r with hBdef
  have hB : MeasurableSet B := measurableSet_closedBall
  have hμB' : intervalMeasure B ≤ ENNReal.ofReal (2 * r) := by
    rw [← Real.volume_closedBall]
    exact Measure.restrict_apply_le _ _
  have hμB : intervalMeasure B ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμB'
  let h : GroupSpace := indicatorConstLp 2 hB hμB Real.pi
  have hreal : intervalMeasure.real B ≤ 2 * r := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hμB'
  have hhn : ‖h‖ ^ 2 ≤ Real.pi ^ 2 * (2 * r) := by
    have e : ‖h‖ = ‖Real.pi‖ * intervalMeasure.real B ^ (1 / (2 : ℝ≥0∞).toReal) :=
      norm_indicatorConstLp (by norm_num) (by norm_num)
    have hsq : (intervalMeasure.real B ^ (1 / (2 : ℝ))) ^ 2 = intervalMeasure.real B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul measureReal_nonneg]; norm_num
    rw [e, mul_pow, Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat, hsq]
    exact mul_le_mul_of_nonneg_left hreal (by positivity)
  have hhρ : ‖h‖ < ρ := by
    have : ‖h‖ ^ 2 < ρ ^ 2 := lt_of_le_of_lt hhn hsmall
    exact lt_of_pow_lt_pow_left₀ 2 hρ.le this
  have hu := hb h hhρ
  rw [g61b_phase_zero] at hu
  set u : HilbertSpace := phaseAction h xi + phaseAction (-h) xi - (2 : ℝ) • xi with hudef
  have hxm : Measurable (fun t => ENNReal.ofReal (‖xi t‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((Lp.stronglyMeasurable xi).measurable.norm.pow_const 2)
  have hae : ∀ᵐ t ∂intervalMeasure, ‖(u : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) =
      B.indicator (fun t => 16 * ENNReal.ofReal (‖xi t‖ ^ 2)) t := by
    filter_upwards [Lp.coeFn_sub (phaseAction h xi + phaseAction (-h) xi) ((2 : ℝ) • xi),
      Lp.coeFn_add (phaseAction h xi) (phaseAction (-h) xi), Lp.coeFn_smul (2 : ℝ) xi,
      (MemLp.coeFn_toLp _ : (phaseAction h xi : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct h xi),
      (MemLp.coeFn_toLp _ :
        (phaseAction (-h) xi : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct (-h) xi),
      Lp.coeFn_neg h,
      (indicatorConstLp_coeFn : (h : ℝ → ℝ) =ᵐ[intervalMeasure] B.indicator fun _ => Real.pi)]
      with t e1 e2 e3 e4 e5 e6 e7
    have hut : (u : ℝ → ℂ) t = (Complex.exp (Complex.I * ((h : ℝ → ℝ) t : ℂ)) +
        Complex.exp (Complex.I * (-((h : ℝ → ℝ) t) : ℝ)) - 2) * xi t := by
      have e4' : (phaseAction h xi : ℝ → ℂ) t = phaseProduct h xi t := e4
      have e5' : (phaseAction (-h) xi : ℝ → ℂ) t = phaseProduct (-h) xi t := e5
      rw [hudef, e1, Pi.sub_apply, e2, Pi.add_apply, e3, Pi.smul_apply, e4', e5']
      simp only [phaseProduct, e6, Pi.neg_apply]
      rw [Complex.real_smul]
      push_cast; ring
    rw [hut, e7]
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      have ex1 : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
        rw [mul_comm]; exact Complex.exp_pi_mul_I
      have ex2 : Complex.exp (Complex.I * ((-Real.pi : ℝ) : ℂ)) = -1 := by
        push_cast
        rw [mul_neg, Complex.exp_neg, ex1]; norm_num
      rw [ex1, ex2, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
        (by norm_num), show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      rw [norm_mul]
      norm_num
      rw [mul_pow]; norm_num
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      simp only [neg_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      norm_num
  have hX : eLpNorm (u : ℝ → ℂ) 2 intervalMeasure =
      (∫⁻ t, B.indicator (fun t => 16 * ENNReal.ofReal (‖xi t‖ ^ 2)) t ∂intervalMeasure)
        ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    rw [lintegral_congr_ae hae]
  set Y := ∫⁻ y in B, I.indicator (fun t => ENNReal.ofReal (‖xi t‖ ^ 2)) y with hY
  have hXY : ∫⁻ t, B.indicator (fun t => 16 * ENNReal.ofReal (‖xi t‖ ^ 2)) t ∂intervalMeasure =
      16 * Y := by
    rw [lintegral_indicator hB, lintegral_const_mul _ hxm, hY, setLIntegral_indicator hI]
    change 16 * ∫⁻ t, _ ∂((volume.restrict I).restrict B) = _
    rw [Measure.restrict_restrict hB, Set.inter_comm]
  rw [hXY] at hX
  have hfin : eLpNorm (u : ℝ → ℂ) 2 intervalMeasure ≠ ∞ := (Lp.eLpNorm_lt_top u).ne
  have hA : ‖u‖ ≤ K * (Real.pi ^ 2 * (2 * r)) :=
    hu.trans (mul_le_mul_of_nonneg_left hhn hK)
  have hofr : eLpNorm (u : ℝ → ℂ) 2 intervalMeasure = ENNReal.ofReal ‖u‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal hfin]
  have h16 : 16 * Y = (eLpNorm (u : ℝ → ℂ) 2 intervalMeasure) ^ (2 : ℝ) := by
    rw [hX, ← ENNReal.rpow_mul]; norm_num
  have hle : 16 * Y ≤ 16 * ENNReal.ofReal ((K ^ 2 * Real.pi ^ 4) * r ^ 2) := by
    rw [h16, hofr, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ ‖u‖ := norm_nonneg _
    have : ‖u‖ ^ (2 : ℝ) = ‖u‖ ^ 2 := by norm_cast
    rw [this]
    have := pow_le_pow_left₀ h0 hA 2
    nlinarith [Real.pi_pos, sq_nonneg (K * Real.pi ^ 2 * r)]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 hle

theorem solution :
    Continuous (fun z : GroupSpace × HilbertSpace => phaseAction z.1 z.2) ∧
      smoothVectors = ({0} : Set HilbertSpace) := by
  refine ⟨g61b_cont, ?_⟩
  ext xi
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hs
    obtain ⟨K, ρ, hK, hρ, hb⟩ := g61b_second (fun f : GroupSpace => phaseAction f xi) (hs 2)
    apply g61b_zero_of_small xi (K ^ 2 * Real.pi ^ 4) (by positivity)
    intro lam _
    have hpos : 0 < ρ ^ 2 / (2 * Real.pi ^ 2) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos] with r hr
    apply g61b_ball xi K ρ hK hρ hb lam r hr.1
    have := hr.2
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  · rintro rfl n
    have : (fun f : GroupSpace => phaseAction f (0 : HilbertSpace)) = fun _ => 0 := by
      funext f; exact g61b_act_zero f
    rw [this]
    exact contDiff_const
