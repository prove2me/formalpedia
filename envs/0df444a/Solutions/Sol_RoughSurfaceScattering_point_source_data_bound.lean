-- Prove2me | solution 1 for RoughSurfaceScattering.point_source_data_bound
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T01:52:23.000855+00:00
-- url     : https://prove2.me/submissions/b911e7b2-93b9-403e-9594-26b08eb409d9

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Metric Filter Topology InnerProductSpace
open RoughSurfaceScattering



noncomputable def Lam (w : R2) : ℝ := ‖w‖ ^ 2 * Real.log (‖w‖ ^ 2)

noncomputable def Lam' (w : R2) : R2 →L[ℝ] ℝ :=
  (Real.log (‖w‖ ^ 2) + 1) • (2 • innerSL ℝ w)

lemma Lam_eq (w : R2) : Lam w = ‖w‖ * (2 * (‖w‖ * Real.log ‖w‖)) := by
  rw [Lam, Real.log_pow]; push_cast; ring

lemma norm_Lam' (w : R2) : ‖Lam' w‖ = 2 * |2 * (‖w‖ * Real.log ‖w‖) + ‖w‖| := by
  rw [Lam', two_nsmul, ← two_smul ℝ, norm_smul, norm_smul, innerSL_apply_norm,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_two, Real.log_pow]
  rw [show |(↑(2:ℕ) * Real.log ‖w‖ + 1)| * (2 * ‖w‖) = 2 * (|(↑(2:ℕ) * Real.log ‖w‖ + 1)| * ‖w‖)
    by ring, ← abs_of_nonneg (norm_nonneg w), ← abs_mul, abs_of_nonneg (norm_nonneg w)]
  push_cast; ring_nf

lemma tendsto_mul_log_norm :
    Tendsto (fun w : R2 => ‖w‖ * Real.log ‖w‖) (𝓝 0) (𝓝 0) := by
  have h := (Real.continuous_mul_log.comp continuous_norm).tendsto (0 : R2)
  simpa [Function.comp_def] using h

lemma Lam_hasFDerivAt (w : R2) : HasFDerivAt Lam (Lam' w) w := by
  by_cases hw : w = 0
  · subst hw
    have h0 : Lam' 0 = 0 := by simp [Lam']
    rw [h0, hasFDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, sub_zero]
    have hL0 : Lam 0 = 0 := by simp [Lam]
    rw [hL0]
    simp only [sub_zero]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have := tendsto_mul_log_norm.eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < c / 2))
    filter_upwards [this] with h hh
    rw [Real.dist_eq, sub_zero] at hh
    simp only [ContinuousLinearMap.zero_apply, sub_zero]
    rw [Lam_eq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg h), abs_mul, abs_two]
    nlinarith [norm_nonneg h]
  · have hN : ‖w‖ ^ 2 ≠ 0 := by positivity
    have := (Real.hasDerivAt_mul_log hN).comp_hasFDerivAt w (hasStrictFDerivAt_norm_sq w).hasFDerivAt
    exact this

lemma Lam'_continuous : Continuous Lam' := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    have h0 : Lam' 0 = 0 := by simp [Lam']
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun w => (norm_Lam' w).le) ?_
    have : Tendsto (fun w : R2 => 2 * |2 * (‖w‖ * Real.log ‖w‖) + ‖w‖|) (𝓝 0) (𝓝 (2 * |2 * 0 + ‖(0:R2)‖|)) :=
      ((tendsto_mul_log_norm.const_mul 2).add (continuous_norm.tendsto 0)).abs.const_mul 2
    simpa using this
  · have hN : ‖w‖ ^ 2 ≠ 0 := by positivity
    unfold Lam'
    refine ContinuousAt.smul (f := fun w : R2 => Real.log (‖w‖ ^ 2) + 1) ?_ ((innerSL ℝ (E := R2)).continuous.const_smul (2:ℕ)).continuousAt
    exact ((Real.continuousAt_log hN).comp (f := fun w : R2 => ‖w‖ ^ 2) (by fun_prop)).add continuousAt_const

lemma Lam_contDiff : ContDiff ℝ 1 Lam :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨Lam', Lam'_continuous, Lam_hasFDerivAt⟩



lemma two_innerSL_norm (w : R2) : ‖2 • innerSL ℝ w‖ = 2 * ‖w‖ := by
  rw [two_nsmul, ← two_smul ℝ, norm_smul, Real.norm_two, innerSL_apply_norm]

lemma Lam'_hasFDerivAt (w : R2) (hw : w ≠ 0) :
    ∃ D : R2 →L[ℝ] R2 →L[ℝ] ℝ, HasFDerivAt Lam' D w ∧
      ‖D‖ ≤ 2 * |Real.log (‖w‖ ^ 2) + 1| + 4 := by
  have hN : ‖w‖ ^ 2 ≠ 0 := by positivity
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h1 := (Real.hasDerivAt_log hN).comp_hasFDerivAt w (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hc : HasFDerivAt (fun z : R2 => Real.log (‖z‖ ^ 2) + 1)
      ((‖w‖ ^ 2)⁻¹ • (2 • innerSL ℝ w)) w := h1.add_const 1
  have hT : HasFDerivAt (fun z : R2 => 2 • innerSL ℝ z) (2 • innerSL ℝ (E := R2)) w :=
    (innerSL ℝ (E := R2)).hasFDerivAt.const_smul 2
  have hD := hc.smul hT
  refine ⟨_, hD, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun u v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  have h1 := abs_real_inner_le_norm u v
  have h2 := abs_real_inner_le_norm w u
  have h3 := abs_real_inner_le_norm w v
  have hNpos : 0 < ‖w‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs]
  calc _ ≤ |Real.log (‖w‖ ^ 2) + 1| * (2 * |inner ℝ u v|) +
        (‖w‖ ^ 2)⁻¹ * (2 * |inner ℝ w u|) * (2 * |inner ℝ w v|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hNpos), abs_two]
        have e : ((innerSL ℝ) u) v = inner ℝ u v := rfl
        rw [e, abs_mul (2:ℝ) (inner ℝ w v), abs_two]
    _ ≤ |Real.log (‖w‖ ^ 2) + 1| * (2 * (‖u‖ * ‖v‖)) +
        (‖w‖ ^ 2)⁻¹ * (2 * (‖w‖ * ‖u‖)) * (2 * (‖w‖ * ‖v‖)) := by gcongr
    _ = (2 * |Real.log (‖w‖ ^ 2) + 1| + 4) * ‖u‖ * ‖v‖ := by
        field_simp
        ring

/-- second derivative of `Q * Lam` away from the origin -/
lemma QLam_second (Q : R2 → ℝ) (hQ : ContDiff ℝ 2 Q) (w : R2) (hw : w ≠ 0) :
    ∃ D : R2 →L[ℝ] R2 →L[ℝ] ℝ, HasFDerivAt (fderiv ℝ (fun z => Q z * Lam z)) D w ∧
      ‖D‖ ≤ |Q w| * (2 * |Real.log (‖w‖ ^ 2) + 1| + 4) +
        2 * ‖fderiv ℝ Q w‖ * ‖Lam' w‖ + |Lam w| * ‖fderiv ℝ (fderiv ℝ Q) w‖ := by
  have hQd : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have hQ1 : ContDiff ℝ 1 (fderiv ℝ Q) := hQ.fderiv_right (by norm_num)
  have hQ1d : Differentiable ℝ (fderiv ℝ Q) := hQ1.differentiable (by norm_num)
  have hfd : fderiv ℝ (fun z => Q z * Lam z) = fun z => Q z • Lam' z + Lam z • fderiv ℝ Q z := by
    funext z
    exact ((hQd z).hasFDerivAt.mul (Lam_hasFDerivAt z)).fderiv
  obtain ⟨DL, hDL, hDLb⟩ := Lam'_hasFDerivAt w hw
  rw [hfd]
  have hD := ((hQd w).hasFDerivAt.smul hDL).add ((Lam_hasFDerivAt w).smul (hQ1d w).hasFDerivAt)
  refine ⟨_, hD, ?_⟩
  have hb := hDLb
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun u v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have a1 := DL.le_opNorm₂ u v
  have a2 := (fderiv ℝ Q w).le_opNorm u
  have a3 := (Lam' w).le_opNorm v
  have a4 := (fderiv ℝ (fderiv ℝ Q) w).le_opNorm₂ u v
  have a5 := (Lam' w).le_opNorm u
  have a6 := (fderiv ℝ Q w).le_opNorm v
  rw [Real.norm_eq_abs] at *
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have hQ0 := abs_nonneg (Q w)
  have hL0 := abs_nonneg (Lam w)
  have hn1 := norm_nonneg (fderiv ℝ Q w)
  have hn2 := norm_nonneg (Lam' w)
  have hn3 := norm_nonneg (fderiv ℝ (fderiv ℝ Q) w)
  have hn4 := norm_nonneg DL
  calc _ ≤ |Q w| * |DL u v| + |fderiv ℝ Q w u| * |Lam' w v| +
        (|Lam w| * |fderiv ℝ (fderiv ℝ Q) w u v| + |Lam' w u| * |fderiv ℝ Q w v|) := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_)
          ((abs_add_le _ _).trans ?_)) <;> rw [abs_mul, abs_mul]
    _ ≤ |Q w| * ((2 * |Real.log (‖w‖ ^ 2) + 1| + 4) * ‖u‖ * ‖v‖) +
        (‖fderiv ℝ Q w‖ * ‖u‖) * (‖Lam' w‖ * ‖v‖) +
        (|Lam w| * (‖fderiv ℝ (fderiv ℝ Q) w‖ * ‖u‖ * ‖v‖) +
          (‖Lam' w‖ * ‖u‖) * (‖fderiv ℝ Q w‖ * ‖v‖)) := by
        gcongr
        exact a1.trans (by gcongr)
    _ = _ := by ring



lemma integrableOn_norm_sub_inv (y : R2) :
    IntegrableOn (fun x : R2 => ‖x - y‖ ^ (-1 : ℝ)) (ball y 1) := by
  have hg : IntegrableOn (fun w : R2 => ‖w‖ ^ (-1 : ℝ)) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := 1)
      (by simp [finrank_euclideanSpace]) (by simp [finrank_euclideanSpace])
      (Eventually.of_forall fun w => ?_) ?_
    · rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  have h1 := ((integrable_indicator_iff measurableSet_ball).mpr hg).comp_sub_right y
  rw [← integrable_indicator_iff measurableSet_ball]
  have e : (ball y 1).indicator (fun x : R2 => ‖x - y‖ ^ (-1 : ℝ)) =
      fun t => (ball 0 1).indicator (fun w : R2 => ‖w‖ ^ (-1 : ℝ)) (t - y) := by
    funext x
    simp only [Set.indicator, mem_ball, dist_eq_norm, sub_zero]
  rw [e]; exact h1

lemma memLp_log_bound (y : R2) (f : R2 → ℂ) (K : ℝ) (p : ENNReal) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hf : AEStronglyMeasurable f (volume.restrict (ball y 1)))
    (hb : ∀ x ∈ ball y 1, x ≠ y → ‖f x‖ ≤ K * (1 + |Real.log ‖x - y‖|)) :
    MemLp f p (volume.restrict (ball y 1)) := by
  set P := p.toReal with hPdef
  have hP : 1 ≤ P := by
    have := ENNReal.toReal_mono hp hp1
    simpa using this
  have hP0 : 0 < P := by linarith
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp1; simp at hp1
  rw [← integrable_norm_rpow_iff hf hp0 hp]
  set M := (|K| * (1 + P)) ^ P
  refine Integrable.mono' ((integrableOn_norm_sub_inv y).const_mul M)
    (hf.norm.aemeasurable.pow_const P).aestronglyMeasurable ?_
  have hne : ∀ᵐ x ∂(volume.restrict (ball y 1)), x ≠ y := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton y
  filter_upwards [hne, ae_restrict_mem measurableSet_ball] with x hxy hx
  set r := ‖x - y‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hr1 : r < 1 := by rw [mem_ball, dist_eq_norm] at hx; exact hx
  have hl := Real.abs_log_mul_self_rpow_lt r (1 / P) hr0 hr1.le (by positivity)
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr0 _), one_div_one_div] at hl
  have hinv : r ^ (1 / P) * r ^ (-1 / P) = 1 := by
    rw [← Real.rpow_add hr0]; ring_nf; exact Real.rpow_zero r
  have hpos' : 0 < r ^ (-1 / P) := Real.rpow_pos_of_pos hr0 _
  have hlog : |Real.log r| ≤ P * r ^ (-1 / P) := by
    have := mul_lt_mul_of_pos_right hl hpos'
    rw [mul_assoc, hinv, mul_one] at this
    exact this.le
  have hone : 1 ≤ r ^ (-1 / P) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1.le (by
      rw [neg_div]; exact neg_nonpos.mpr (by positivity))
  have hfx : ‖f x‖ ≤ |K| * (1 + P) * r ^ (-1 / P) := by
    calc ‖f x‖ ≤ K * (1 + |Real.log r|) := hb x hx hxy
      _ ≤ |K| * (1 + |Real.log r|) := by
          gcongr
          exact le_abs_self K
      _ ≤ |K| * (r ^ (-1 / P) + P * r ^ (-1 / P)) := by gcongr
      _ = _ := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖f x‖ ^ P ≤ (|K| * (1 + P) * r ^ (-1 / P)) ^ P :=
        Real.rpow_le_rpow (norm_nonneg _) hfx hP0.le
    _ = M * r ^ (-1 : ℝ) := by
        rw [Real.mul_rpow (by positivity) hpos'.le, ← Real.rpow_mul hr0.le]
        congr 2
        field_simp



lemma contDiff_powerSeries (c : ℕ → ℝ)
    (hc : ∀ r : ℝ, 0 ≤ r → Summable fun n => |c n| * r ^ n) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun t : ℝ => ∑' n, c n * t ^ n) := by
  set p := FormalMultilinearSeries.ofScalars ℝ c
  have hrad : p.radius = ⊤ := by
    refine p.radius_eq_top_of_summable_norm fun r => ?_
    refine ((hc r r.2)).congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
  have hps := p.hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
  have han : AnalyticOnNhd ℝ p.sum Set.univ := by
    intro y _
    exact hps.analyticAt_of_mem (by rw [hrad]; simp)
  have hsum : p.sum = fun t : ℝ => ∑' n, c n * t ^ n := by
    funext t
    simp only [FormalMultilinearSeries.sum, p, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
  rw [← hsum]
  exact han.contDiff
lemma harmonic_le_self (n : ℕ) : (harmonic n : ℝ) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]
    push_cast
    have : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
    linarith

lemma harmonic_nonneg' (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  unfold harmonic
  push_cast
  exact Finset.sum_nonneg fun i _ => by positivity

/-- Coefficients of `J₀(x) = P_J((x/2)²)`. -/
noncomputable def cJ (m : ℕ) : ℝ := (-1 : ℝ) ^ m / ((m.factorial : ℝ) ^ 2)

/-- Coefficients of the series part of `Y₀`: `∑ (-1)^m H_{m+1} (x/2)^{2(m+1)}/((m+1)!)² =
t · P_S(t)` with `t = (x/2)²`. -/
noncomputable def cS (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m * (harmonic (m + 1) : ℝ) / (((m + 1).factorial : ℝ) ^ 2)

noncomputable def PJ (t : ℝ) : ℝ := ∑' m, cJ m * t ^ m
noncomputable def PS (t : ℝ) : ℝ := ∑' m, cS m * t ^ m

lemma fact_sq_ge (m : ℕ) : (m.factorial : ℝ) ≤ (m.factorial : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr m.factorial_ne_zero
  nlinarith

lemma contDiff_PJ {n : WithTop ℕ∞} : ContDiff ℝ n PJ := by
  refine contDiff_powerSeries cJ (fun r hr => ?_)
  refine (Real.summable_pow_div_factorial r).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [cJ, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity),
    div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_left (by positivity) hf (fact_sq_ge n)

lemma contDiff_PS {n : WithTop ℕ∞} : ContDiff ℝ n PS := by
  refine contDiff_powerSeries cS (fun r hr => ?_)
  refine (Real.summable_pow_div_factorial r).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hH := harmonic_le_self (n + 1)
  have hH0 := harmonic_nonneg' (n + 1)
  have hfs : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
    push_cast [Nat.factorial_succ]; ring
  rw [cS, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hH0,
    abs_of_pos (by positivity), hfs]
  have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  push_cast at hH hn1 ⊢
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hf]
  have h1 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.factorial_ne_zero
  have hr0 : 0 ≤ r ^ n := by positivity
  have ha : (harmonic (n + 1) : ℝ) * n.factorial ≤ (n + 1) * n.factorial :=
    mul_le_mul_of_nonneg_right hH (by positivity)
  have hx1 : (1 : ℝ) ≤ (n + 1) * n.factorial := by nlinarith
  have hb : ((n : ℝ) + 1) * n.factorial ≤ ((n + 1) * n.factorial) ^ 2 := by nlinarith
  have : (harmonic (n + 1) : ℝ) * n.factorial ≤ ((n + 1) * n.factorial) ^ 2 := ha.trans hb
  nlinarith

lemma besselJ0_eq (x : ℝ) : besselJ0 x = PJ ((x / 2) ^ 2) := by
  unfold besselJ0 PJ cJ
  congr 1; funext m
  rw [← pow_mul]; ring

lemma besselY0_eq (x : ℝ) :
    besselY0 x = 2 / Real.pi * (Real.log (x / 2) + Real.eulerMascheroniConstant) *
      PJ ((x / 2) ^ 2) + 2 / Real.pi * ((x / 2) ^ 2 * PS ((x / 2) ^ 2)) := by
  unfold besselY0
  rw [besselJ0_eq]
  congr 2
  unfold PS cS
  rw [← tsum_mul_left]
  congr 1; funext m
  rw [← pow_mul, pow_succ]; ring

/-- `t = (k|y|/2)²`. -/
noncomputable def tq (k : ℝ) (y : R2) : ℝ := (k * ‖y‖ / 2) ^ 2

/-- Smooth factor in front of the logarithmic singularity: `a(y) = J₀(k|y|)`. -/
noncomputable def aF (k : ℝ) (y : R2) : ℂ := (PJ (tq k y) : ℂ)

/-- Smooth remainder `b(y)` of `Φ_k`. -/
noncomputable def bF (k : ℝ) (y : R2) : ℂ :=
  (Complex.I / 4 - (((Real.log (k / 2) + Real.eulerMascheroniConstant) / (2 * Real.pi) : ℝ) : ℂ)) *
    (PJ (tq k y) : ℂ) - (((1 / (2 * Real.pi)) * (tq k y * PS (tq k y)) : ℝ) : ℂ)

lemma contDiff_tq (k : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (tq k) := by
  have : tq k = fun y : R2 => (k ^ 2 / 4) * ‖y‖ ^ 2 := by
    funext y; unfold tq; ring
  rw [this]
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

lemma contDiff_bF (k : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (bF k) := by
  have h1 : ContDiff ℝ n (fun y : R2 => (PJ (tq k y) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_PJ.comp (contDiff_tq k))
  have h2 : ContDiff ℝ n (fun y : R2 =>
      (((1 / (2 * Real.pi)) * (tq k y * PS (tq k y)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((contDiff_tq k).mul (contDiff_PS.comp (contDiff_tq k))))
  exact (contDiff_const.mul h1).sub h2

lemma aF_zero (k : ℝ) : aF k 0 = 1 := by
  simp only [aF, tq, norm_zero, mul_zero, zero_div]
  norm_num [PJ, cJ]
  rw [tsum_eq_single 0]
  · simp
  · intro m hm; simp [zero_pow hm]

/-- `Φ_k(x,z) = a(x-z) Φ₀(x,z) + b(x-z)` away from the source point. -/
lemma phi_decomp (k : ℝ) (hk : 0 < k) (x z : R2) (hx : x ≠ z) :
    Phi k x z = aF k (x - z) * Phi 0 x z + bF k (x - z) := by
  have hr : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hlog : Real.log (k * ‖x - z‖ / 2) = Real.log ‖x - z‖ + Real.log (k / 2) := by
    rw [show k * ‖x - z‖ / 2 = ‖x - z‖ * (k / 2) by ring,
      Real.log_mul hr.ne' (by positivity)]
  have hlog2 : Real.log (1 / ‖x - z‖) = -Real.log ‖x - z‖ := by rw [one_div, Real.log_inv]
  simp only [Phi, hk.ne', if_false, if_true, hankel01, aF, bF, tq]
  rw [besselJ0_eq, besselY0_eq, hlog, hlog2]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring


lemma abs_cJ_le (m : ℕ) : |cJ m| ≤ 1 / (m.factorial : ℝ) := by
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  rw [cJ, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
  exact div_le_div_of_nonneg_left (by positivity) hf (fact_sq_ge m)

lemma summable_cJ (x : ℝ) : Summable fun m => cJ m * x ^ m := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |x|) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, div_eq_mul_one_div, mul_comm (|x| ^ m)]
  exact mul_le_mul_of_nonneg_right (abs_cJ_le m) (by positivity)

noncomputable def dJ (A B : ℝ) (m : ℕ) : ℝ := cJ (m + 1) * (A ^ (m + 1) - B ^ (m + 1))

noncomputable def qJ (A B : ℝ) (t : ℝ) : ℝ := ∑' m, dJ A B m * t ^ m

lemma contDiff_qJ (A B : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (qJ A B) := by
  refine contDiff_powerSeries (dJ A B) (fun r hr => ?_)
  have hs := ((Real.summable_pow_div_factorial (|A| * r)).mul_left |A|).add
    ((Real.summable_pow_div_factorial (|B| * r)).mul_left |B|)
  refine hs.of_nonneg_of_le (fun m => by positivity) fun m => ?_
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have h1 : |cJ (m + 1)| ≤ 1 / (m.factorial : ℝ) := by
    refine (abs_cJ_le (m + 1)).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) hf (by exact_mod_cast Nat.factorial_le (by omega))
  have h2 : |A ^ (m + 1) - B ^ (m + 1)| ≤ |A| * |A| ^ m + |B| * |B| ^ m := by
    refine (abs_sub _ _).trans ?_
    rw [abs_pow, abs_pow, pow_succ', pow_succ']
  calc |dJ A B m| * r ^ m ≤ (1 / (m.factorial : ℝ)) * (|A| * |A| ^ m + |B| * |B| ^ m) * r ^ m := by
        rw [dJ, abs_mul]; gcongr
    _ = _ := by rw [mul_pow, mul_pow]; field_simp

lemma PJ_sub (A B t : ℝ) : PJ (A * t) - PJ (B * t) = t * qJ A B t := by
  unfold PJ qJ
  rw [← (summable_cJ (A * t)).tsum_sub (summable_cJ (B * t))]
  have hs : Summable fun m => cJ m * (A * t) ^ m - cJ m * (B * t) ^ m :=
    (summable_cJ (A * t)).sub (summable_cJ (B * t))
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, sub_self, zero_add]
  congr 1; funext m
  rw [dJ]; ring

noncomputable def bG (k : ℝ) (w : R2) : ℂ := if k = 0 then 0 else bF k w

lemma contDiff_bG (k : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (bG k) := by
  unfold bG
  by_cases hk : k = 0
  · simp only [hk, if_true]; exact contDiff_const
  · simp only [hk, if_false]; exact contDiff_bF k

lemma aF_eq (k : ℝ) (w : R2) : aF k w = (PJ (k ^ 2 / 4 * ‖w‖ ^ 2) : ℂ) := by
  unfold aF tq; congr 2; ring

lemma phi0_eq (x z : R2) :
    Phi 0 x z = ((-(1 / (4 * Real.pi)) * Real.log (‖x - z‖ ^ 2) : ℝ) : ℂ) := by
  simp only [Phi, if_true]
  congr 1
  rw [Real.log_pow, one_div, one_div, Real.log_inv]; push_cast; field_simp; ring

lemma phi_decomp' (k : ℝ) (hk : 0 ≤ k) (x z : R2) (hx : x ≠ z) :
    Phi k x z = aF k (x - z) * Phi 0 x z + bG k (x - z) := by
  rcases hk.lt_or_eq with hk | hk
  · rw [phi_decomp k hk x z hx]; simp [bG, hk.ne']
  · subst hk
    have : aF 0 (x - z) = 1 := by
      rw [aF_eq, ← aF_zero 0, aF_eq]; simp
    simp [this, bG]

lemma phi_diff_eq (k k1 : ℝ) (hk : 0 ≤ k) (hk1 : 0 ≤ k1) (x y : R2) (hx : x ≠ y) :
    Phi k1 x y - Phi k x y =
      ((-(1 / (4 * Real.pi)) * (qJ (k1 ^ 2 / 4) (k ^ 2 / 4) (‖x - y‖ ^ 2) * Lam (x - y)) : ℝ) : ℂ) +
        (bG k1 (x - y) - bG k (x - y)) := by
  rw [phi_decomp' k1 hk1 x y hx, phi_decomp' k hk x y hx, aF_eq, aF_eq, phi0_eq]
  have key := PJ_sub (k1 ^ 2 / 4) (k ^ 2 / 4) (‖x - y‖ ^ 2)
  have keyC : (PJ (k1 ^ 2 / 4 * ‖x - y‖ ^ 2) : ℂ) - (PJ (k ^ 2 / 4 * ‖x - y‖ ^ 2) : ℂ) =
      ((‖x - y‖ ^ 2 * qJ (k1 ^ 2 / 4) (k ^ 2 / 4) (‖x - y‖ ^ 2) : ℝ) : ℂ) := by
    rw [← key]; push_cast; ring
  unfold Lam
  push_cast
  push_cast at keyC
  linear_combination (-(1 / (4 * (Real.pi : ℂ))) * (Real.log (‖x - y‖ ^ 2) : ℂ)) * keyC



lemma phi0_contDiffOn2 (z : R2) :
    ContDiffOn ℝ 2 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
  intro x hx
  have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ContDiffAt ℝ 2 (fun x' : R2 => ‖x' - z‖) x :=
    (contDiffAt_norm ℝ hx').comp x ((contDiffAt_id).sub contDiffAt_const)
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr hx'
  have hinv : ContDiffAt ℝ 2 (fun x' : R2 => 1 / ‖x' - z‖) x := by
    have := (contDiffAt_inv ℝ hpos.ne').comp x hn
    simpa [one_div, Function.comp_def] using this
  have hlog : ContDiffAt ℝ 2 (fun x' : R2 => Real.log (1 / ‖x' - z‖)) x :=
    (Real.contDiffAt_log.mpr (by positivity)).comp x hinv
  have hreal : ContDiffAt ℝ 2
      (fun x' : R2 => 1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖)) x :=
    contDiffAt_const.mul hlog
  have hc : ContDiffAt ℝ 2
      (fun x' : R2 => ((1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  simpa [Phi] using hc.contDiffWithinAt

lemma phi_contDiffOn2 (k : ℝ) (hk : 0 ≤ k) (z : R2) :
    ContDiffOn ℝ 2 (fun x => Phi k x z) {x | x ≠ z} := by
  have hs : ContDiff ℝ 2 (fun x : R2 => x - z) := contDiff_id.sub contDiff_const
  have haF : ContDiff ℝ 2 (aF k) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_PJ.comp (contDiff_tq k))
  have h1 : ContDiffOn ℝ 2 (fun x => aF k (x - z) * Phi 0 x z + bG k (x - z)) {x | x ≠ z} :=
    ((haF.comp hs).contDiffOn.mul (phi0_contDiffOn2 z)).add ((contDiff_bG k).comp hs).contDiffOn
  exact h1.congr fun x hx => phi_decomp' k hk x z hx

theorem dcd (k : ℝ) (hk : 0 ≤ k) (z ν : R2) :
    ContDiffOn ℝ 1 (dipoleSource k z ν) {x | x ≠ z} := by
  have hU : IsOpen {x : R2 | x ≠ z} := isOpen_ne
  have h := (phi_contDiffOn2 k hk z).fderiv_of_isOpen hU (m := 1) (by norm_num)
  exact h.clm_apply contDiffOn_const



noncomputable def PsiK (k : ℝ) (w : R2) : ℂ :=
  ((-(1 / (4 * Real.pi)) * (qJ (k ^ 2 / 4) ((0 : ℝ) ^ 2 / 4) (‖w‖ ^ 2) * Lam w) : ℝ) : ℂ) +
    (bG k w - bG 0 w)

lemma PsiK_contDiff (k : ℝ) : ContDiff ℝ 1 (PsiK k) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
    (((contDiff_qJ _ _).comp (contDiff_norm_sq ℝ)).mul Lam_contDiff))).add
    ((contDiff_bG k).sub (contDiff_bG 0))

lemma PsiK_eq (k : ℝ) (hk : 0 ≤ k) (x z : R2) (h : x ≠ z) :
    Phi k x z - Phi 0 x z = PsiK k (x - z) :=
  phi_diff_eq 0 k le_rfl hk x z h

lemma bound_closedBall {E : Type*} [NormedAddCommGroup E] (R : ℝ) (f : R2 → E)
    (hf : Continuous f) : ∃ M ≥ (0 : ℝ), ∀ w ∈ closedBall (0 : R2) R, ‖f w‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : R2) R).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun w hw => (hC w hw).trans (le_max_left _ _)⟩

lemma PsiK_second (k R : ℝ) : ∃ K ≥ (0 : ℝ), ∀ e w : R2, w ≠ 0 → ‖w‖ ≤ R →
    ∃ G : R2 →L[ℝ] ℂ, HasFDerivAt (fun z => fderiv ℝ (PsiK k) z e) G w ∧
      ‖G‖ ≤ K * (1 + |Real.log ‖w‖|) * ‖e‖ := by
  set c : ℝ := -(1 / (4 * Real.pi)) with hc
  set Q : R2 → ℝ := fun w => qJ (k ^ 2 / 4) ((0 : ℝ) ^ 2 / 4) (‖w‖ ^ 2) with hQdef
  have hQ : ContDiff ℝ 2 Q := (contDiff_qJ _ _).comp (contDiff_norm_sq ℝ)
  set F : R2 → ℝ := fun w => Q w * Lam w with hFdef
  have hF : ContDiff ℝ 1 F := (hQ.of_le (by norm_num)).mul Lam_contDiff
  set Bd : R2 → ℂ := fun w => bG k w - bG 0 w with hBddef
  have hBd : ContDiff ℝ 2 Bd := (contDiff_bG k).sub (contDiff_bG 0)
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hBdd : Differentiable ℝ Bd := hBd.differentiable (by norm_num)
  have hBd1 : ContDiff ℝ 1 (fderiv ℝ Bd) := hBd.fderiv_right (by norm_num)
  have hPsi : PsiK k = (⇑Complex.ofRealCLM ∘ fun y => c * F y) + Bd := by
    funext w; simp [PsiK, hc, hFdef, hQdef, hBddef]
  have hΨfd : ∀ (w e : R2), fderiv ℝ (PsiK k) w e =
      ((c * fderiv ℝ F w e : ℝ) : ℂ) + fderiv ℝ Bd w e := by
    intro w e
    have h := (Complex.ofRealCLM.hasFDerivAt.comp w ((hFd w).hasFDerivAt.const_mul c)).add
      (hBdd w).hasFDerivAt
    rw [hPsi, h.fderiv]
    simp
  obtain ⟨M, hM0, hM⟩ := bound_closedBall R (fun w => (Q w, fderiv ℝ Q w, fderiv ℝ (fderiv ℝ Q) w))
    (hQ.continuous.prodMk ((hQ.continuous_fderiv (by norm_num)).prodMk
      ((hQ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero)))
  obtain ⟨ML, hML0, hML⟩ := bound_closedBall R (fun w => (Lam w, Lam' w))
    (Lam_contDiff.continuous.prodMk Lam'_continuous)
  obtain ⟨MB, hMB0, hMB⟩ := bound_closedBall R (fderiv ℝ (fderiv ℝ Bd))
    (hBd1.continuous_fderiv one_ne_zero)
  refine ⟨|c| * (6 * M + 3 * M * ML) + MB + 4 * |c| * M, by positivity, ?_⟩
  intro e w hw hwR
  obtain ⟨D, hD, hDb⟩ := QLam_second Q hQ w hw
  have h1 : HasFDerivAt (fun z => fderiv ℝ F z e) ((ContinuousLinearMap.apply ℝ ℝ e).comp D) w :=
    (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp w hD
  have h2 : HasFDerivAt (fun z => fderiv ℝ Bd z e)
      ((ContinuousLinearMap.apply ℝ ℂ e).comp (fderiv ℝ (fderiv ℝ Bd) w)) w :=
    (ContinuousLinearMap.apply ℝ ℂ e).hasFDerivAt.comp w
      ((hBd1.differentiable one_ne_zero) w).hasFDerivAt
  have h3 := (Complex.ofRealCLM.hasFDerivAt.comp w (h1.const_mul c)).add h2
  have heq : (fun z => fderiv ℝ (PsiK k) z e) =
      fun z => Complex.ofRealCLM (c * fderiv ℝ F z e) + fderiv ℝ Bd z e := by
    funext z; rw [hΨfd]; rfl
  rw [heq]
  refine ⟨_, h3, ?_⟩
  have hwB : w ∈ closedBall (0 : R2) R := by rw [mem_closedBall, dist_zero_right]; exact hwR
  have hMw := hM w hwB
  have hMLw := hML w hwB
  have hQw : |Q w| ≤ M := by
    rw [← Real.norm_eq_abs]; exact (norm_fst_le _).trans hMw
  have hQ1w : ‖fderiv ℝ Q w‖ ≤ M := ((norm_fst_le _).trans (norm_snd_le _)).trans hMw
  have hQ2w : ‖fderiv ℝ (fderiv ℝ Q) w‖ ≤ M :=
    ((norm_snd_le _).trans (norm_snd_le _)).trans hMw
  have hLw : |Lam w| ≤ ML := by rw [← Real.norm_eq_abs]; exact (norm_fst_le _).trans hMLw
  have hL1w : ‖Lam' w‖ ≤ ML := (norm_snd_le _).trans hMLw
  have hDb' : ‖D‖ ≤ M * (4 * |Real.log ‖w‖| + 6) + 3 * M * ML := by
    refine hDb.trans ?_
    have hlog : |Real.log (‖w‖ ^ 2) + 1| ≤ 2 * |Real.log ‖w‖| + 1 := by
      rw [Real.log_pow]; push_cast
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two, abs_one]
    have := abs_nonneg (Real.log ‖w‖)
    calc _ ≤ M * (2 * (2 * |Real.log ‖w‖| + 1) + 4) + 2 * M * ML + ML * M := by gcongr
    _ = _ := by ring
  have hBw := hMB w hwB
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, Complex.ofRealCLM_apply]
  have e1 : (c • (ContinuousLinearMap.apply ℝ ℝ e).comp D) u = c * D u e := by simp
  rw [e1]
  have a1 := D.le_opNorm₂ u e
  have a2 := (fderiv ℝ (fderiv ℝ Bd) w).le_opNorm₂ u e
  rw [Real.norm_eq_abs] at a1
  have hu := norm_nonneg u
  have he := norm_nonneg e
  have hL := abs_nonneg (Real.log ‖w‖)
  have hc0 := abs_nonneg c
  calc _ ≤ ‖((c * D u e : ℝ) : ℂ)‖ + ‖fderiv ℝ (fderiv ℝ Bd) w u e‖ := norm_add_le _ _
    _ ≤ |c| * (‖D‖ * ‖u‖ * ‖e‖) + MB * ‖u‖ * ‖e‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        gcongr
        exact a2.trans (by gcongr)
    _ ≤ |c| * ((M * (4 * |Real.log ‖w‖| + 6) + 3 * M * ML) * ‖u‖ * ‖e‖) + MB * ‖u‖ * ‖e‖ := by
        gcongr
    _ ≤ _ := by
        have h4 : 0 ≤ 4 * |c| * M * ‖u‖ * ‖e‖ := by positivity
        have h5 : 0 ≤ (|c| * (6 * M + 3 * M * ML) + MB) * |Real.log ‖w‖| * ‖u‖ * ‖e‖ := by
          positivity
        have : (|c| * (6 * M + 3 * M * ML) + MB + 4 * |c| * M) * (1 + |Real.log ‖w‖|) * ‖e‖ * ‖u‖ -
            (|c| * ((M * (4 * |Real.log ‖w‖| + 6) + 3 * M * ML) * ‖u‖ * ‖e‖) + MB * ‖u‖ * ‖e‖) =
            4 * |c| * M * ‖u‖ * ‖e‖ +
              (|c| * (6 * M + 3 * M * ML) + MB) * |Real.log ‖w‖| * ‖u‖ * ‖e‖ := by ring
        linarith



noncomputable def Pser (c : ℕ → ℝ) (s : ℝ) : ℝ := ∑' m, c m * s ^ m

def Entire (c : ℕ → ℝ) : Prop := ∀ r : ℝ, 0 ≤ r → Summable fun m => |c m| * r ^ m

def Dco (c : ℕ → ℝ) (m : ℕ) : ℝ := ((m : ℝ) + 1) * c (m + 1)

def Sh (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => c m

lemma Entire.summable {c : ℕ → ℝ} (hc : Entire c) (s : ℝ) : Summable fun m => c m * s ^ m :=
  Summable.of_norm_bounded (hc |s| (abs_nonneg _)) fun m => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]

lemma Entire.dco {c : ℕ → ℝ} (hc : Entire c) : Entire (Dco c) := by
  intro r hr
  have h := (summable_nat_add_iff 1).mpr (hc (2 * (r + 1)) (by positivity))
  refine h.of_nonneg_of_le (fun m => by positivity) fun m => ?_
  simp only [_root_.Dco]
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (m : ℝ) + 1)]
  have h1 : ((m : ℝ) + 1) ≤ 2 ^ (m + 1) := by
    have := Nat.lt_two_pow_self (n := m + 1)
    exact_mod_cast this.le
  have h2 : r ^ m ≤ (r + 1) ^ (m + 1) :=
    (pow_le_pow_left₀ hr (by linarith) m).trans (pow_le_pow_right₀ (by linarith) (by omega))
  calc ((m : ℝ) + 1) * |c (m + 1)| * r ^ m = |c (m + 1)| * (((m : ℝ) + 1) * r ^ m) := by ring
    _ ≤ |c (m + 1)| * (2 ^ (m + 1) * (r + 1) ^ (m + 1)) := by gcongr
    _ = |c (m + 1)| * (2 * (r + 1)) ^ (m + 1) := by rw [mul_pow]

lemma Entire.sh {c : ℕ → ℝ} (hc : Entire c) : Entire (Sh c) := by
  intro r hr
  rw [← summable_nat_add_iff 1]
  refine ((hc r hr).mul_left r).congr fun m => ?_
  simp only [_root_.Sh, pow_succ]; ring

lemma mul_Pser {c : ℕ → ℝ} (hc : Entire c) (s : ℝ) : s * Pser c s = Pser (Sh c) s := by
  unfold Pser
  rw [(hc.sh.summable s).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [Sh, zero_mul, zero_add]
  congr 1; funext m; ring

lemma hasDerivAt_Pser {c : ℕ → ℝ} (hc : Entire c) (s : ℝ) :
    HasDerivAt (Pser c) (Pser (Dco c) s) s := by
  set R := |s| + 1
  have hR : 0 < R := by positivity
  have hsum : Summable fun m => |c m| * ((m : ℝ) * R ^ (m - 1)) := by
    rw [← summable_nat_add_iff 1]
    refine (hc.dco R hR.le).congr fun m => ?_
    simp only [Dco, Nat.add_sub_cancel]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (m : ℝ) + 1)]
    push_cast; ring
  have h := hasDerivAt_tsum_of_isPreconnected (g := fun m y => c m * y ^ m)
    (g' := fun m y => c m * ((m : ℝ) * y ^ (m - 1))) hsum isOpen_ball (convex_ball 0 R).isPreconnected
    (fun m y _ => (hasDerivAt_pow m y).const_mul (c m))
    (fun m y hy => by
      rw [mem_ball, dist_zero_right] at hy
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
      gcongr
      exact hy.le)
    (mem_ball_self hR) (hc.summable 0)
    (by rw [mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith)
  have hs' : Summable fun m => c m * ((m : ℝ) * s ^ (m - 1)) := by
    rw [← summable_nat_add_iff 1]
    refine ((hc.dco).summable s).congr fun m => ?_
    simp only [Dco, Nat.add_sub_cancel]; push_cast; ring
  have e : (∑' m, c m * ((m : ℝ) * s ^ (m - 1))) = Pser (Dco c) s := by
    rw [hs'.tsum_eq_zero_add]
    simp only [Pser, Dco, Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
    congr 1; funext m; push_cast; ring
  rw [← e]; exact h

lemma entire_of_le (c : ℕ → ℝ) (h : ∀ m, |c m| ≤ 1 / (m.factorial : ℝ)) : Entire c := by
  intro r hr
  refine (Real.summable_pow_div_factorial r).of_nonneg_of_le (fun m => by positivity) fun m => ?_
  calc |c m| * r ^ m ≤ 1 / (m.factorial : ℝ) * r ^ m := by gcongr; exact h m
    _ = r ^ m / m.factorial := by ring

lemma entire_cJ : Entire cJ := entire_of_le cJ abs_cJ_le

lemma entire_cS : Entire cS := by
  refine entire_of_le cS fun m => ?_
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hH := harmonic_le_self (m + 1)
  have hH0 := harmonic_nonneg' (m + 1)
  have hfs : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
    push_cast [Nat.factorial_succ]; ring
  rw [cS, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hH0,
    abs_of_pos (by positivity), hfs]
  push_cast at hH
  have h1 : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr m.factorial_ne_zero
  rw [div_le_div_iff₀ (by positivity) hf]
  have : (harmonic (m + 1) : ℝ) * m.factorial ≤ ((m : ℝ) + 1) * m.factorial :=
    mul_le_mul_of_nonneg_right hH (by positivity)
  have hX : (1 : ℝ) ≤ ((m : ℝ) + 1) * m.factorial := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hX (by linarith : (0:ℝ) ≤ ((m : ℝ) + 1) * m.factorial)]

/-- Bessel ODE for `P_J`: `(s P_J')' = -P_J`. -/
lemma coeff_J (m : ℕ) : Dco (Sh (Dco cJ)) m = -cJ m := by
  simp only [Dco, Sh, cJ]
  have hfs : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  push_cast
  rw [hfs, pow_succ]
  field_simp

/-- the `Y₀` series part: `(s Q')' + Q = -P_J'` with `Q = Sh cS` -/
lemma coeff_S (m : ℕ) : Dco (Sh (Dco (Sh cS))) m = -(Sh cS m) - Dco cJ m := by
  cases m with
  | zero =>
    simp [Dco, Sh, cS, cJ, harmonic]
  | succ n =>
    simp only [Dco, Sh, cS, cJ]
    have hf1 : ((n + 1 + 1).factorial : ℝ) = (n + 2) * (n + 1).factorial := by
      push_cast [Nat.factorial_succ]; ring
    have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast (n + 1).factorial_pos
    have hH : (harmonic (n + 1 + 1) : ℝ) = harmonic (n + 1) + 1 / ((n : ℝ) + 2) := by
      rw [harmonic_succ]; push_cast; ring
    rw [hH, hf1]
    push_cast
    field_simp
    ring



/-- `Δ (G ∘ |· - z|²) = 4 (t G'(t))'` at `t = |x - z|²`. -/
lemma lap_radial (G G1 : ℝ → ℝ) (z x : R2) (d : ℝ)
    (hG : ∀ᶠ t in 𝓝 (‖x - z‖ ^ 2), HasDerivAt G (G1 t) t)
    (hG1 : DifferentiableAt ℝ G1 (‖x - z‖ ^ 2))
    (hd : HasDerivAt (fun t => t * G1 t) d (‖x - z‖ ^ 2)) :
    Laplacian.laplacian (fun y : R2 => G (‖y - z‖ ^ 2)) x = 4 * d := by
  set N : R2 → ℝ := fun y => ‖y - z‖ ^ 2 with hNdef
  have hN : ∀ y, HasFDerivAt N (2 • innerSL ℝ (y - z)) y := fun y =>
    (((hasFDerivAt_id y).sub_const z).norm_sq).congr_fderiv (by ext v; simp)
  set g2 := deriv G1 (N x)
  have hg2 : HasDerivAt G1 g2 (N x) := hG1.hasDerivAt
  have hd' : d = G1 (N x) + N x * g2 := by
    have := (hasDerivAt_id (N x)).mul hg2
    simp only [id, one_mul] at this
    exact hd.unique this
  set T : R2 → (R2 →L[ℝ] ℝ) := fun y => G1 (N y) • (2 • innerSL ℝ (y - z)) with hT
  have hev : ∀ᶠ y in 𝓝 x, HasDerivAt G (G1 (N y)) (N y) :=
    ((hN x).continuousAt.eventually hG)
  have hfd : fderiv ℝ (fun y => G (N y)) =ᶠ[𝓝 x] T := by
    filter_upwards [hev] with y hy
    exact (hy.comp_hasFDerivAt y (hN y)).fderiv
  have hc : HasFDerivAt (fun y => G1 (N y)) (g2 • (2 • innerSL ℝ (x - z))) x :=
    hg2.comp_hasFDerivAt x (hN x)
  have hlin := (((innerSL ℝ (E := R2)).hasFDerivAt (x := x - z)).comp x
    ((hasFDerivAt_id x).sub_const z)).const_smul 2
  have hTd := hc.smul hlin
  have hTd' : HasFDerivAt T (G1 (N x) • (2 • (innerSL ℝ (E := R2)).comp (ContinuousLinearMap.id ℝ R2)) +
      (g2 • (2 • innerSL ℝ (x - z))).smulRight (2 • innerSL ℝ (x - z))) x := hTd
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [iteratedFDeriv_two_apply]
  rw [show (fun y : R2 => G (‖y - z‖ ^ 2)) = fun y => G (N y) from rfl, hfd.fderiv_eq, hTd'.fderiv]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.basisFun_apply]
  have hNx : N x = (x - z) 0 ^ 2 + (x - z) 1 ^ 2 := by
    simp only [hNdef, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] 
  rw [hd', hNx]
  simp only [PiLp.sub_apply]
  ring



noncomputable def PJ1 : ℝ → ℝ := Pser (Dco cJ)
noncomputable def Qs : ℝ → ℝ := Pser (Sh cS)
noncomputable def Q1 : ℝ → ℝ := Pser (Dco (Sh cS))

lemma Pser_neg (c : ℕ → ℝ) (s : ℝ) : Pser (fun m => -c m) s = -Pser c s := by
  unfold Pser; rw [← tsum_neg]; congr 1; funext m; ring

lemma hasDerivAt_PJ (s : ℝ) : HasDerivAt PJ (PJ1 s) s := hasDerivAt_Pser entire_cJ s
lemma hasDerivAt_PJ1 (s : ℝ) : HasDerivAt PJ1 (Pser (Dco (Dco cJ)) s) s :=
  hasDerivAt_Pser entire_cJ.dco s
lemma hasDerivAt_Qs (s : ℝ) : HasDerivAt Qs (Q1 s) s := hasDerivAt_Pser entire_cS.sh s
lemma hasDerivAt_Q1 (s : ℝ) : HasDerivAt Q1 (Pser (Dco (Dco (Sh cS))) s) s :=
  hasDerivAt_Pser entire_cS.sh.dco s

lemma thetaJ (s : ℝ) : HasDerivAt (fun s => s * PJ1 s) (-PJ s) s := by
  have e : (fun s => s * PJ1 s) = Pser (Sh (Dco cJ)) := funext fun s => mul_Pser entire_cJ.dco s
  rw [e]
  have h := hasDerivAt_Pser entire_cJ.dco.sh s
  have e2 : Pser (Dco (Sh (Dco cJ))) s = -PJ s := by
    rw [show Dco (Sh (Dco cJ)) = fun m => -cJ m from funext coeff_J, Pser_neg]; rfl
  rwa [e2] at h

lemma thetaQ (s : ℝ) : HasDerivAt (fun s => s * Q1 s) (-Qs s - PJ1 s) s := by
  have e : (fun s => s * Q1 s) = Pser (Sh (Dco (Sh cS))) :=
    funext fun s => mul_Pser entire_cS.sh.dco s
  rw [e]
  have h := hasDerivAt_Pser entire_cS.sh.dco.sh s
  have e2 : Pser (Dco (Sh (Dco (Sh cS)))) s = -Qs s - PJ1 s := by
    rw [show Dco (Sh (Dco (Sh cS))) = fun m => -(Sh cS m) - Dco cJ m from funext coeff_S]
    unfold Pser Qs PJ1 Pser
    rw [← tsum_neg, ← (entire_cS.sh.summable s).neg.tsum_sub (entire_cJ.dco.summable s)]
    congr 1; funext m; ring
  rwa [e2] at h

lemma Qs_eq (s : ℝ) : s * PS s = Qs s := mul_Pser entire_cS s

lemma diff_PJ1 : Differentiable ℝ PJ1 := fun s => (hasDerivAt_PJ1 s).differentiableAt
lemma diff_Q1 : Differentiable ℝ Q1 := fun s => (hasDerivAt_Q1 s).differentiableAt

/-- the real radial profiles -/
noncomputable def ell (t : ℝ) : ℝ := -(1 / (4 * Real.pi)) * Real.log t
noncomputable def ell1 (t : ℝ) : ℝ := -(1 / (4 * Real.pi)) * t⁻¹
noncomputable def Jt (A t : ℝ) : ℝ := PJ (A * t)
noncomputable def J1t (A t : ℝ) : ℝ := A * PJ1 (A * t)
noncomputable def Rt (A t : ℝ) : ℝ := Jt A t * ell t + -(1 / (2 * Real.pi)) * Qs (A * t)
noncomputable def R1t (A t : ℝ) : ℝ :=
  J1t A t * ell t + Jt A t * ell1 t + -(1 / (2 * Real.pi)) * (A * Q1 (A * t))

lemma hasDerivAt_ell (t : ℝ) (ht : t ≠ 0) : HasDerivAt ell (ell1 t) t :=
  (Real.hasDerivAt_log ht).const_mul _

lemma hasDerivAt_Jt (A t : ℝ) : HasDerivAt (Jt A) (J1t A t) t := by
  have := (hasDerivAt_PJ (A * t)).comp t ((hasDerivAt_id t).const_mul A)
  exact this.congr_deriv (by simp only [J1t]; ring)

lemma hasDerivAt_Rt (A t : ℝ) (ht : t ≠ 0) : HasDerivAt (Rt A) (R1t A t) t := by
  have hQ := (hasDerivAt_Qs (A * t)).comp t ((hasDerivAt_id t).const_mul A)
  have := ((hasDerivAt_Jt A t).mul (hasDerivAt_ell t ht)).add (hQ.const_mul (-(1 / (2 * Real.pi))))
  exact this.congr_deriv (by simp only [R1t]; ring)

lemma ode_Jt (A t : ℝ) : HasDerivAt (fun t => t * J1t A t) (-A * Jt A t) t := by
  have h := (thetaJ (A * t)).comp t ((hasDerivAt_id t).const_mul A)
  have e : (fun t => t * J1t A t) = (fun s => s * PJ1 s) ∘ fun t => A * id t := by
    funext t; simp [J1t]; ring
  rw [e]; exact h.congr_deriv (by simp only [Jt]; ring)

lemma ode_Rt (A t : ℝ) (ht : 0 < t) : HasDerivAt (fun t => t * R1t A t) (-A * Rt A t) t := by
  set F : ℝ → ℝ := fun t => ((A * t) * PJ1 (A * t)) * ell t + Jt A t * (-(1 / (4 * Real.pi))) +
    -(1 / (2 * Real.pi)) * ((A * t) * Q1 (A * t))
  have hev : F =ᶠ[𝓝 t] fun t => t * R1t A t := by
    filter_upwards [lt_mem_nhds ht] with u hu
    simp only [F, R1t, J1t, ell1]
    field_simp
  have hθJ := (thetaJ (A * t)).comp t ((hasDerivAt_id t).const_mul A)
  have hθQ := (thetaQ (A * t)).comp t ((hasDerivAt_id t).const_mul A)
  have hF : HasDerivAt F ((-PJ (A * t) * (A * 1)) * ell t + ((A * t) * PJ1 (A * t)) * ell1 t +
      J1t A t * (-(1 / (4 * Real.pi))) +
      -(1 / (2 * Real.pi)) * ((-Qs (A * t) - PJ1 (A * t)) * (A * 1))) t := by
    have := ((hθJ.mul (hasDerivAt_ell t ht.ne')).add
      ((hasDerivAt_Jt A t).mul_const (-(1 / (4 * Real.pi))))).add
      (hθQ.const_mul (-(1 / (2 * Real.pi))))
    simp only [Function.comp_def, id] at this
    exact this
  refine (hF.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  simp only [Rt, Jt, J1t, ell, ell1]
  field_simp
  ring

lemma ode_ell (t : ℝ) (ht : 0 < t) : HasDerivAt (fun t => t * ell1 t) 0 t := by
  refine (hasDerivAt_const t (-(1 / (4 * Real.pi)))).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with u hu
  simp only [ell1]; field_simp

lemma contDiff_Qs {n : WithTop ℕ∞} : ContDiff ℝ n Qs := by
  have : Qs = fun s => s * PS s := funext fun s => (Qs_eq s).symm
  rw [this]; exact contDiff_id.mul contDiff_PS



lemma contDiffAt_radial (G : ℝ → ℝ) (z x : R2) (hG : ContDiffAt ℝ 2 G (‖x - z‖ ^ 2)) :
    ContDiffAt ℝ 2 (fun y : R2 => G (‖y - z‖ ^ 2)) x :=
  hG.comp x ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt

lemma lap_ofReal (u : R2 → ℝ) (x : R2) (hu : ContDiffAt ℝ 2 u x) :
    Laplacian.laplacian (fun y => ((u y : ℝ) : ℂ)) x = ((Laplacian.laplacian u x : ℝ) : ℂ) := by
  have := hu.laplacian_CLM_comp_left (l := Complex.ofRealCLM)
  simpa [Function.comp_def] using this

theorem phh (k : ℝ) (hk : 0 ≤ k) (z : R2) :
    IsHelmholtzOn {x | x ≠ z} k (fun x => Phi k x z) := by
  intro x hx
  have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
  set T := ‖x - z‖ ^ 2 with hT
  have hTpos : 0 < T := by positivity
  have hlogc : ContDiffAt ℝ 2 ell T :=
    contDiffAt_const.mul (Real.contDiffAt_log.mpr hTpos.ne')
  have hell_ev : ∀ᶠ t in 𝓝 T, HasDerivAt ell (ell1 t) t := by
    filter_upwards [lt_mem_nhds hTpos] with t ht
    exact hasDerivAt_ell t ht.ne'
  have hell1d : DifferentiableAt ℝ ell1 T :=
    (differentiableAt_const _).mul (differentiableAt_inv hTpos.ne')
  rcases hk.lt_or_eq with hk | hk
  · -- `k > 0`
    set A : ℝ := k ^ 2 / 4
    set β : ℂ := Complex.I / 4 -
      (((Real.log (k / 2) + Real.eulerMascheroniConstant) / (2 * Real.pi) : ℝ) : ℂ)
    have hloc : (fun y => Phi k y z) =ᶠ[𝓝 x]
        fun y => ((Rt A (‖y - z‖ ^ 2) : ℝ) : ℂ) + β * ((Jt A (‖y - z‖ ^ 2) : ℝ) : ℂ) := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      rw [phi_decomp k hk y z hy, aF_eq, phi0_eq]
      simp only [bF, Rt, Jt, ell, β, A]
      have htq : tq k (y - z) = k ^ 2 / 4 * ‖y - z‖ ^ 2 := by unfold tq; ring
      rw [htq, ← Qs_eq]
      push_cast
      ring
    rw [(laplacian_congr_nhds hloc).eq_of_nhds, show (fun x => Phi k x z) x = _ from hloc.eq_of_nhds]
    have hJc : ContDiffAt ℝ 2 (Jt A) T :=
      (contDiff_PJ.comp (contDiff_const.mul contDiff_id)).contDiffAt
    have hRc : ContDiffAt ℝ 2 (Rt A) T :=
      (hJc.mul hlogc).add (contDiffAt_const.mul
        (contDiff_Qs.comp (contDiff_const.mul contDiff_id)).contDiffAt)
    have h1 := contDiffAt_radial (Rt A) z x hRc
    have h2 := contDiffAt_radial (Jt A) z x hJc
    have hc1 : ContDiffAt ℝ 2 (fun y => ((Rt A (‖y - z‖ ^ 2) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x h1
    have hc2 : ContDiffAt ℝ 2 (fun y => ((Jt A (‖y - z‖ ^ 2) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x h2
    have hadd := hc1.laplacian_add (hc2.const_smul β)
    simp only [Pi.add_def, smul_eq_mul] at hadd
    rw [hadd]
    have hsm := laplacian_smul (f := fun y => ((Jt A (‖y - z‖ ^ 2) : ℝ) : ℂ)) β hc2
    simp only [Pi.smul_def, smul_eq_mul] at hsm
    rw [hsm, lap_ofReal _ x h1, lap_ofReal _ x h2]
    have hR := lap_radial (Rt A) (R1t A) z x (-A * Rt A T)
      (by filter_upwards [lt_mem_nhds hTpos] with t ht; exact hasDerivAt_Rt A t ht.ne')
      (by
        have hlin : DifferentiableAt ℝ (fun t : ℝ => A * t) T :=
          (differentiableAt_const A).mul differentiableAt_id
        have hP := (diff_PJ1 (A * T)).comp T hlin
        have hQ := (diff_Q1 (A * T)).comp T hlin
        have hl := (hasDerivAt_ell T hTpos.ne').differentiableAt
        have hJd := (hasDerivAt_Jt A T).differentiableAt
        exact ((((differentiableAt_const A).mul hP).mul hl).add (hJd.mul hell1d)).add
          ((differentiableAt_const _).mul ((differentiableAt_const A).mul hQ)))
      (ode_Rt A T hTpos)
    have hJ := lap_radial (Jt A) (J1t A) z x (-A * Jt A T)
      (Eventually.of_forall fun t => hasDerivAt_Jt A t)
      ((differentiableAt_const A).mul ((diff_PJ1 (A * T)).comp T
        ((differentiableAt_const A).mul differentiableAt_id)))
      (ode_Jt A T)
    rw [hR, hJ]
    simp only [A]
    push_cast
    ring
  · -- `k = 0`
    subst hk
    have hloc : (fun y => Phi 0 y z) = fun y => ((ell (‖y - z‖ ^ 2) : ℝ) : ℂ) := by
      funext y; rw [phi0_eq]; rfl
    rw [hloc, lap_ofReal _ x (contDiffAt_radial ell z x hlogc),
      lap_radial ell ell1 z x 0 hell_ev hell1d (ode_ell T hTpos)]
    simp



lemma energy_bound (G G1 : ℝ → ℝ) (A : ℝ) (hA : 0 < A) (t0 : ℝ) (ht0 : 0 < t0)
    (hG : ∀ t, 0 < t → HasDerivAt G (G1 t) t) (hG1 : ∀ t, 0 < t → DifferentiableAt ℝ G1 t)
    (hode : ∀ t, 0 < t → HasDerivAt (fun t => t * G1 t) (-A * G t) t) :
    ∃ M, ∀ t, t0 ≤ t → |G t| ≤ M ∧ |G1 t| * Real.sqrt t ≤ M := by
  set E : ℝ → ℝ := fun t => A * G t ^ 2 + t * G1 t ^ 2 with hE
  have hEd : ∀ t, 0 < t → HasDerivAt E (-(G1 t) ^ 2) t := by
    intro t ht
    have hg2 := (hG1 t ht).hasDerivAt
    have hrel : -A * G t = G1 t + t * deriv G1 t := by
      have := (hasDerivAt_id t).mul hg2
      simp only [id, one_mul] at this
      exact (hode t ht).unique this
    have h := (((hG t ht).pow 2).const_mul A).add ((hasDerivAt_id t).mul (hg2.pow 2))
    refine h.congr_deriv ?_
    simp only [id, Nat.cast_ofNat, Pi.pow_apply]
    linear_combination (-2 * G1 t) * hrel
  have hanti : AntitoneOn E (Set.Ici t0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici t0) ?_ ?_ ?_
    · exact fun t ht => (hEd t (lt_of_lt_of_le ht0 ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hEd t (lt_trans ht0 ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hEd t (lt_trans ht0 ht)).deriv]
      nlinarith [sq_nonneg (G1 t)]
  refine ⟨Real.sqrt (E t0 / A) + Real.sqrt (E t0), fun t ht => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le ht0 ht
  have hEt : E t ≤ E t0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have h1 : A * G t ^ 2 ≤ E t0 := by
    have : 0 ≤ t * G1 t ^ 2 := by positivity
    simp only [hE] at hEt ⊢; linarith
  have h2 : t * G1 t ^ 2 ≤ E t0 := by
    have : 0 ≤ A * G t ^ 2 := by positivity
    simp only [hE] at hEt ⊢; linarith
  constructor
  · have : |G t| ≤ Real.sqrt (E t0 / A) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hA]; linarith)
    linarith [Real.sqrt_nonneg (E t0)]
  · have : |G1 t| * Real.sqrt t ≤ Real.sqrt (E t0) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith [Real.sqrt_nonneg (E t0 / A)]

lemma R1t_diff (A t : ℝ) (ht : 0 < t) : DifferentiableAt ℝ (R1t A) t := by
  have hlin : DifferentiableAt ℝ (fun t : ℝ => A * t) t :=
    (differentiableAt_const A).mul differentiableAt_id
  have hP := (diff_PJ1 (A * t)).comp t hlin
  have hQ := (diff_Q1 (A * t)).comp t hlin
  have hl := (hasDerivAt_ell t ht.ne').differentiableAt
  have hJd := (hasDerivAt_Jt A t).differentiableAt
  have hl1 : DifferentiableAt ℝ ell1 t := (differentiableAt_const _).mul (differentiableAt_inv ht.ne')
  exact ((((differentiableAt_const A).mul hP).mul hl).add (hJd.mul hl1)).add
    ((differentiableAt_const _).mul ((differentiableAt_const A).mul hQ))

lemma J1t_diff (A t : ℝ) : DifferentiableAt ℝ (J1t A) t :=
  (differentiableAt_const A).mul ((diff_PJ1 (A * t)).comp t
    ((differentiableAt_const A).mul differentiableAt_id))

theorem pba (k : ℝ) (hk : 0 < k) (z : R2) (d : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, ∀ x : R2, d ≤ ‖x - z‖ →
      ‖Phi k x z‖ ≤ C ∧ ‖fderiv ℝ (fun x' => Phi k x' z) x‖ ≤ C := by
  set A : ℝ := k ^ 2 / 4
  have hA : 0 < A := by positivity
  set β : ℂ := Complex.I / 4 -
    (((Real.log (k / 2) + Real.eulerMascheroniConstant) / (2 * Real.pi) : ℝ) : ℂ)
  obtain ⟨MR, hMR⟩ := energy_bound (Rt A) (R1t A) A hA (d ^ 2) (by positivity)
    (fun t ht => hasDerivAt_Rt A t ht.ne') (fun t ht => R1t_diff A t ht) (fun t ht => ode_Rt A t ht)
  obtain ⟨MJ, hMJ⟩ := energy_bound (Jt A) (J1t A) A hA (d ^ 2) (by positivity)
    (fun t _ => hasDerivAt_Jt A t) (fun t _ => J1t_diff A t) (fun t _ => ode_Jt A t)
  have hMR0 : 0 ≤ MR := (abs_nonneg _).trans (hMR (d ^ 2) le_rfl).1
  have hMJ0 : 0 ≤ MJ := (abs_nonneg _).trans (hMJ (d ^ 2) le_rfl).1
  refine ⟨3 * (MR + ‖β‖ * MJ), fun x hx => ?_⟩
  have hxz : x ≠ z := by
    intro h; rw [h, sub_self, norm_zero] at hx; linarith
  set t := ‖x - z‖ ^ 2 with htdef
  have htpos : 0 < t := by have : 0 < ‖x - z‖ := by linarith
                           positivity
  have ht0 : d ^ 2 ≤ t := by rw [htdef]; gcongr
  have hsq : Real.sqrt t = ‖x - z‖ := by rw [htdef, Real.sqrt_sq (norm_nonneg _)]
  have hloc : (fun y => Phi k y z) =ᶠ[𝓝 x]
      fun y => ((Rt A (‖y - z‖ ^ 2) : ℝ) : ℂ) + β * ((Jt A (‖y - z‖ ^ 2) : ℝ) : ℂ) := by
    filter_upwards [isOpen_ne.mem_nhds hxz] with y hy
    rw [phi_decomp k hk y z hy, aF_eq, phi0_eq]
    simp only [bF, Rt, Jt, ell, β, A]
    have htq : tq k (y - z) = k ^ 2 / 4 * ‖y - z‖ ^ 2 := by unfold tq; ring
    rw [htq, ← Qs_eq]
    push_cast
    ring
  obtain ⟨hR1, hR2⟩ := hMR t ht0
  obtain ⟨hJ1, hJ2⟩ := hMJ t ht0
  have hβ := norm_nonneg β
  constructor
  · rw [hloc.eq_of_nhds]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hJ1 hβ
    nlinarith
  · have hN : ∀ y, HasFDerivAt (fun y : R2 => ‖y - z‖ ^ 2) (2 • innerSL ℝ (y - z)) y := fun y =>
      (((hasFDerivAt_id y).sub_const z).norm_sq).congr_fderiv (by ext v; simp)
    have hRx := (hasDerivAt_Rt A t htpos.ne').comp_hasFDerivAt x (hN x)
    have hJx := (hasDerivAt_Jt A t).comp_hasFDerivAt x (hN x)
    have hsum := (Complex.ofRealCLM.hasFDerivAt.comp x hRx).add
      ((Complex.ofRealCLM.hasFDerivAt.comp x hJx).const_mul β)
    rw [hloc.fderiv_eq]
    have hsum' : HasFDerivAt (fun y => ((Rt A (‖y - z‖ ^ 2) : ℝ) : ℂ) + β * ((Jt A (‖y - z‖ ^ 2) : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (R1t A t • (2 • innerSL ℝ (x - z))) +
          β • Complex.ofRealCLM.comp (J1t A t • (2 • innerSL ℝ (x - z)))) x := hsum
    rw [hsum'.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, nsmul_eq_mul,
      innerSL_apply_apply, Nat.cast_ofNat]
    have hin := abs_real_inner_le_norm (x - z) v
    have hv := norm_nonneg v
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul, abs_two]
    rw [hsq] at hR2 hJ2
    have e1 : |R1t A t| * (2 * |@inner ℝ R2 _ (x - z) v|) ≤ 2 * MR * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left hin (abs_nonneg (R1t A t))
      nlinarith
    have e2 : |J1t A t| * (2 * |@inner ℝ R2 _ (x - z) v|) ≤ 2 * MJ * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left hin (abs_nonneg (J1t A t))
      nlinarith
    have := mul_le_mul_of_nonneg_left e2 hβ
    rw [show |2 * @inner ℝ R2 _ (x - z) v| = 2 * |@inner ℝ R2 _ (x - z) v| by
      rw [abs_mul, abs_two]]
    nlinarith [mul_nonneg hMR0 hv, mul_nonneg (mul_nonneg hβ hMJ0) hv]



lemma abs_sub_le_gpt (f : ℝ → ℝ) (s t : ℝ) : |s - t| ≤ ‖gpt f s - gpt f t‖ := by
  have h := EuclideanSpace.norm_sq_eq (gpt f s - gpt f t)
  rw [Fin.sum_univ_two] at h
  have e0 : (gpt f s - gpt f t) 0 = s - t := by simp [gpt, pt]
  rw [e0] at h
  have h0 : |s - t| ^ 2 ≤ ‖gpt f s - gpt f t‖ ^ 2 := by
    rw [h, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg ‖(gpt f s - gpt f t) 1‖]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

/-- Lipschitz at short range plus bounded gives `1/2`-Hölder in the distance on `Γ`. -/
lemma holder_of_lip {E : Type*} [NormedAddCommGroup E] (f : ℝ → ℝ) (φ : ℝ → E)
    (hc : Continuous φ) (B : ℝ) (hB : ∀ s, ‖φ s‖ ≤ B) (ρ L : ℝ) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hlip : ∀ s t, ‖gpt f s - gpt f t‖ < ρ → ‖φ s - φ t‖ ≤ L * ‖gpt f s - gpt f t‖) :
    IsBC0AlphaGam f (1 / 2) φ := by
  refine ⟨hc, ⟨B, hB⟩, L * Real.sqrt ρ + 2 * B / Real.sqrt ρ, fun s t => ?_⟩
  set r := ‖gpt f s - gpt f t‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  rw [← Real.sqrt_eq_rpow]
  have hsr := Real.sqrt_nonneg r
  rcases lt_or_ge r ρ with h | h
  · calc ‖φ s - φ t‖ ≤ L * r := hlip s t h
      _ = L * (Real.sqrt r * Real.sqrt r) := by rw [Real.mul_self_sqrt hr0]
      _ ≤ L * (Real.sqrt ρ * Real.sqrt r) := by
          gcongr
      _ ≤ (L * Real.sqrt ρ + 2 * B / Real.sqrt ρ) * Real.sqrt r := by
          have : 0 ≤ 2 * B / Real.sqrt ρ * Real.sqrt r := by positivity
          nlinarith
  · have h1 : ‖φ s - φ t‖ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith [hB s, hB t])
    have h2 : Real.sqrt ρ ≤ Real.sqrt r := Real.sqrt_le_sqrt h
    have h3 : 2 * B ≤ 2 * B / Real.sqrt ρ * Real.sqrt r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsρ]; nlinarith
    have : 0 ≤ L * Real.sqrt ρ * Real.sqrt r := by positivity
    nlinarith

/-- Products of bounded Hölder functions are bounded Hölder. -/
lemma IsBC0AlphaGam.mul (f : ℝ → ℝ) (α : ℝ) {φ ψ : ℝ → ℂ} (hφ : IsBC0AlphaGam f α φ)
    (hψ : IsBC0AlphaGam f α ψ) : IsBC0AlphaGam f α (fun s => φ s * ψ s) := by
  obtain ⟨hc1, ⟨B1, hB1⟩, H1, hH1⟩ := hφ
  obtain ⟨hc2, ⟨B2, hB2⟩, H2, hH2⟩ := hψ
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  refine ⟨hc1.mul hc2, ⟨B1 * B2, fun s => ?_⟩, B1 * H2 + B2 * H1, fun s t => ?_⟩
  · rw [norm_mul]; exact mul_le_mul (hB1 s) (hB2 s) (norm_nonneg _) hB10
  · have e : φ s * ψ s - φ t * ψ t = φ s * (ψ s - ψ t) + ψ t * (φ s - φ t) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hr := Real.rpow_nonneg (norm_nonneg (gpt f s - gpt f t)) α
    calc ‖φ s‖ * ‖ψ s - ψ t‖ + ‖ψ t‖ * ‖φ s - φ t‖ ≤
        B1 * (H2 * ‖gpt f s - gpt f t‖ ^ α) + B2 * (H1 * ‖gpt f s - gpt f t‖ ^ α) := by
          gcongr
          · exact hB1 s
          · exact hH2 s t
          · exact hB2 t
          · exact hH1 s t
      _ = _ := by ring

lemma IsBC0AlphaGam.add (f : ℝ → ℝ) (α : ℝ) {E : Type*} [NormedAddCommGroup E] {φ ψ : ℝ → E}
    (hφ : IsBC0AlphaGam f α φ) (hψ : IsBC0AlphaGam f α ψ) :
    IsBC0AlphaGam f α (fun s => φ s + ψ s) := by
  obtain ⟨hc1, ⟨B1, hB1⟩, H1, hH1⟩ := hφ
  obtain ⟨hc2, ⟨B2, hB2⟩, H2, hH2⟩ := hψ
  refine ⟨hc1.add hc2, ⟨B1 + B2, fun s => (norm_add_le _ _).trans (add_le_add (hB1 s) (hB2 s))⟩,
    H1 + H2, fun s t => ?_⟩
  have e : φ s + ψ s - (φ t + ψ t) = (φ s - φ t) + (ψ s - ψ t) := by abel
  rw [e]
  exact (norm_add_le _ _).trans (by linarith [hH1 s t, hH2 s t])

lemma IsBC0AlphaGam.neg (f : ℝ → ℝ) (α : ℝ) {E : Type*} [NormedAddCommGroup E] {φ : ℝ → E}
    (hφ : IsBC0AlphaGam f α φ) : IsBC0AlphaGam f α (fun s => -φ s) := by
  obtain ⟨hc1, ⟨B1, hB1⟩, H1, hH1⟩ := hφ
  refine ⟨hc1.neg, ⟨B1, fun s => by rw [norm_neg]; exact hB1 s⟩, H1, fun s t => ?_⟩
  rw [show -φ s - -φ t = -(φ s - φ t) by abel, norm_neg]; exact hH1 s t



section radial
variable (G1 G2 G3 : ℝ → ℝ) (z ν : R2)

noncomputable def pD (x : R2) : ℝ := 2 * G1 (‖x - z‖ ^ 2) * @inner ℝ R2 _ (x - z) ν

noncomputable def vD (e : R2) (x : R2) : ℝ :=
  4 * G2 (‖x - z‖ ^ 2) * @inner ℝ R2 _ (x - z) ν * @inner ℝ R2 _ (x - z) e +
    2 * G1 (‖x - z‖ ^ 2) * @inner ℝ R2 _ ν e

lemma hasFDerivAt_N (x : R2) :
    HasFDerivAt (fun y : R2 => ‖y - z‖ ^ 2) (2 • innerSL ℝ (x - z)) x :=
  (((hasFDerivAt_id x).sub_const z).norm_sq).congr_fderiv (by ext v; simp)

lemma hasFDerivAt_inner_sub (p x : R2) :
    HasFDerivAt (fun y : R2 => @inner ℝ R2 _ (y - p) ν) (innerSL ℝ ν) x := by
  have h := ((innerSL ℝ ν).hasFDerivAt (x := x - p)).comp x ((hasFDerivAt_id x).sub_const p)
  refine (h.congr_fderiv (by ext v; simp)).congr_of_eventuallyEq ?_
  filter_upwards with y
  simp [real_inner_comm]

lemma pD_hasFDerivAt (hd1 : ∀ t, 0 < t → HasDerivAt G1 (G2 t) t) (x : R2) (hx : x ≠ z) :
    ∃ L : R2 →L[ℝ] ℝ, HasFDerivAt (pD G1 z ν) L x ∧ ∀ e, L e = vD G1 G2 z ν e x := by
  have hN0 : 0 < ‖x - z‖ ^ 2 := by
    have : x - z ≠ 0 := sub_ne_zero.mpr hx
    positivity
  have h1 := (hd1 _ hN0).comp_hasFDerivAt x (hasFDerivAt_N z x)
  have h2 := ((h1.const_mul 2).mul (hasFDerivAt_inner_sub ν z x))
  refine ⟨_, h2, fun e => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat, vD, Function.comp_def]
  rw [real_inner_comm e ν]
  ring

lemma vD_hasFDerivAt (hd1 : ∀ t, 0 < t → HasDerivAt G1 (G2 t) t)
    (hd2 : ∀ t, 0 < t → HasDerivAt G2 (G3 t) t) (e x : R2) (hx : x ≠ z) :
    ∃ L : R2 →L[ℝ] ℝ, HasFDerivAt (vD G1 G2 z ν e) L x ∧ ∀ h, L h =
      8 * G3 (‖x - z‖ ^ 2) * @inner ℝ R2 _ (x - z) h * @inner ℝ R2 _ (x - z) ν *
        @inner ℝ R2 _ (x - z) e +
      4 * G2 (‖x - z‖ ^ 2) * (@inner ℝ R2 _ h ν * @inner ℝ R2 _ (x - z) e +
        @inner ℝ R2 _ (x - z) ν * @inner ℝ R2 _ h e) +
      4 * G2 (‖x - z‖ ^ 2) * @inner ℝ R2 _ (x - z) h * @inner ℝ R2 _ ν e := by
  have hN0 : 0 < ‖x - z‖ ^ 2 := by
    have : x - z ≠ 0 := sub_ne_zero.mpr hx
    positivity
  have hg2 := (hd2 _ hN0).comp_hasFDerivAt x (hasFDerivAt_N z x)
  have hg1 := (hd1 _ hN0).comp_hasFDerivAt x (hasFDerivAt_N z x)
  have hA := (((hg2.const_mul 4).mul (hasFDerivAt_inner_sub ν z x)).mul
    (hasFDerivAt_inner_sub e z x))
  have hB := (hg1.const_mul 2).mul_const (@inner ℝ R2 _ ν e)
  refine ⟨_, hA.add hB, fun h => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat, Function.comp_def, Pi.mul_apply]
  rw [real_inner_comm h ν, real_inner_comm h e]
  ring

end radial



/-- A real function with bounded derivative on `{|x - z| > d/2}`, restricted to `Γ`, is
`1/2`-Hölder when `Γ` stays at distance `≥ d` from `z`. -/
lemma gamma_holder (f : ℝ → ℝ) (hfc : Continuous f) (z : R2) (d : ℝ) (hd : 0 < d)
    (hΓ : ∀ s, d ≤ ‖gpt f s - z‖) (u : R2 → ℝ) (L : R2 → (R2 →L[ℝ] ℝ)) (B K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ x, d / 2 < ‖x - z‖ → HasFDerivAt u (L x) x ∧ ‖L x‖ ≤ K ∧ |u x| ≤ B) :
    IsBC0AlphaGam f (1 / 2) (fun s => ((u (gpt f s) : ℝ) : ℂ)) := by
  have hgc : Continuous (gpt f) := by
    unfold gpt pt
    fun_prop
  have hO : ∀ s, d / 2 < ‖gpt f s - z‖ := fun s => by linarith [hΓ s]
  refine holder_of_lip f _ ?_ B (fun s => ?_) (d / 2) K (by positivity) hK fun s t hst => ?_
  · refine Complex.continuous_ofReal.comp ?_
    rw [continuous_iff_continuousAt]
    intro s
    exact ((hu _ (hO s)).1.continuousAt).comp hgc.continuousAt
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact (hu _ (hO s)).2.2
  · rw [← Complex.ofReal_sub, Complex.norm_real]
    have hball : ∀ y ∈ ball (gpt f s) (d / 2), d / 2 < ‖y - z‖ := by
      intro y hy
      rw [mem_ball, dist_eq_norm] at hy
      have := norm_sub_norm_le (gpt f s - z) (gpt f s - y)
      have e : gpt f s - z - (gpt f s - y) = y - z := by abel
      rw [e] at this
      have h2 : ‖gpt f s - y‖ = ‖y - gpt f s‖ := norm_sub_rev _ _
      linarith [hΓ s]
    have hmv := (convex_ball (gpt f s) (d / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := u) (f' := L) (C := K)
      (fun y hy => (hu y (hball y hy)).1.hasFDerivWithinAt)
      (fun y hy => (hu y (hball y hy)).2.1)
      (mem_ball_self (by positivity : 0 < d / 2))
      (by rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub]; exact hst)
    rw [norm_sub_rev (u (gpt f s)), norm_sub_rev (gpt f s)]
    exact hmv

/-- weighted bounds on the radial factors give bounds for `pD`, `vD` and the derivative of `vD`. -/
lemma radial_dipole_bounds (G1 G2 G3 : ℝ → ℝ) (z ν e : R2) (d : ℝ) (hd : 0 < d)
    (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hd1 : ∀ t, 0 < t → HasDerivAt G1 (G2 t) t) (hd2 : ∀ t, 0 < t → HasDerivAt G2 (G3 t) t)
    (B1 : ∀ t, (d / 2) ^ 2 ≤ t → |G1 t| * Real.sqrt t ≤ M1)
    (B2 : ∀ t, (d / 2) ^ 2 ≤ t → |G2 t| * t ≤ M2)
    (B3 : ∀ t, (d / 2) ^ 2 ≤ t → |G3 t| * (t * Real.sqrt t) ≤ M3) :
    ∀ x, d / 2 < ‖x - z‖ →
      |pD G1 z ν x| ≤ 2 * M1 * ‖ν‖ ∧
      |vD G1 G2 z ν e x| ≤ (4 * M2 + 2 * M1 / (d / 2)) * (‖ν‖ * ‖e‖) ∧
      ∃ L : R2 →L[ℝ] ℝ, HasFDerivAt (vD G1 G2 z ν e) L x ∧
        ‖L‖ ≤ (8 * M3 + 12 * M2 / (d / 2)) * (‖ν‖ * ‖e‖) := by
  intro x hx
  set r := ‖x - z‖ with hr
  have hr0 : 0 < r := by linarith
  have hxz : x ≠ z := fun h => by rw [h, sub_self, norm_zero] at hr; linarith
  have ht : (d / 2) ^ 2 ≤ r ^ 2 := by gcongr
  have hsq : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr0.le
  have b1 := B1 _ ht; have b2 := B2 _ ht; have b3 := B3 _ ht
  rw [hsq] at b1 b3
  have hG1 : |G1 (r ^ 2)| ≤ M1 / (d / 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc |G1 (r ^ 2)| * (d / 2) ≤ |G1 (r ^ 2)| * r := by gcongr
      _ ≤ M1 := b1
  have hG2r : |G2 (r ^ 2)| * r ≤ M2 / (d / 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc |G2 (r ^ 2)| * r * (d / 2) ≤ |G2 (r ^ 2)| * r * r := by gcongr
      _ = |G2 (r ^ 2)| * r ^ 2 := by ring
      _ ≤ M2 := b2
  have hin := fun (a : R2) => abs_real_inner_le_norm (x - z) a
  have hνe := abs_real_inner_le_norm ν e
  have hν := norm_nonneg ν
  have he := norm_nonneg e
  refine ⟨?_, ?_, ?_⟩
  · simp only [pD]
    rw [abs_mul, abs_mul, abs_two]
    have := hin ν
    calc 2 * |G1 (‖x - z‖ ^ 2)| * |@inner ℝ R2 _ (x - z) ν| ≤ 2 * |G1 (r ^ 2)| * (r * ‖ν‖) := by
          gcongr
      _ = 2 * (|G1 (r ^ 2)| * r) * ‖ν‖ := by ring
      _ ≤ 2 * M1 * ‖ν‖ := by gcongr
  · simp only [vD]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_two]
    have h1 := hin ν; have h2 := hin e
    calc 4 * |G2 (‖x - z‖ ^ 2)| * |@inner ℝ R2 _ (x - z) ν| * |@inner ℝ R2 _ (x - z) e| +
          2 * |G1 (‖x - z‖ ^ 2)| * |@inner ℝ R2 _ ν e|
        ≤ 4 * |G2 (r ^ 2)| * (r * ‖ν‖) * (r * ‖e‖) + 2 * (M1 / (d / 2)) * (‖ν‖ * ‖e‖) := by
          gcongr
      _ = 4 * (|G2 (r ^ 2)| * r ^ 2) * (‖ν‖ * ‖e‖) + 2 * (M1 / (d / 2)) * (‖ν‖ * ‖e‖) := by ring
      _ ≤ 4 * M2 * (‖ν‖ * ‖e‖) + 2 * (M1 / (d / 2)) * (‖ν‖ * ‖e‖) := by gcongr
      _ = _ := by ring
  · obtain ⟨L, hL, hLf⟩ := vD_hasFDerivAt G1 G2 G3 z ν hd1 hd2 e x hxz
    refine ⟨L, hL, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_⟩
    rw [hLf h, Real.norm_eq_abs]
    have h1 := hin h; have h2 := hin ν; have h3 := hin e
    have h4 := abs_real_inner_le_norm h ν; have h5 := abs_real_inner_le_norm h e
    have hh := norm_nonneg h
    have hsplit : ∀ a b c : ℝ, |a + b + c| ≤ |a| + |b| + |c| := fun a b c =>
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    refine (hsplit _ _ _).trans ?_
    rw [show (8 * M3 + 12 * M2 / (d / 2)) * (‖ν‖ * ‖e‖) * ‖h‖ =
      8 * M3 * (‖ν‖ * ‖e‖) * ‖h‖ + 8 * (M2 / (d / 2)) * (‖ν‖ * ‖e‖) * ‖h‖ +
        4 * (M2 / (d / 2)) * (‖ν‖ * ‖e‖) * ‖h‖ by ring]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8)]
      calc 8 * |G3 (‖x - z‖ ^ 2)| * |@inner ℝ R2 _ (x - z) h| * |@inner ℝ R2 _ (x - z) ν| *
            |@inner ℝ R2 _ (x - z) e| ≤ 8 * |G3 (r ^ 2)| * (r * ‖h‖) * (r * ‖ν‖) * (r * ‖e‖) := by
            gcongr
        _ = 8 * (|G3 (r ^ 2)| * (r ^ 2 * r)) * (‖ν‖ * ‖e‖) * ‖h‖ := by ring
        _ ≤ 8 * M3 * (‖ν‖ * ‖e‖) * ‖h‖ := by gcongr
    · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)).trans ?_
      rw [abs_mul, abs_mul]
      calc 4 * |G2 (‖x - z‖ ^ 2)| * (|@inner ℝ R2 _ h ν| * |@inner ℝ R2 _ (x - z) e| +
            |@inner ℝ R2 _ (x - z) ν| * |@inner ℝ R2 _ h e|)
          ≤ 4 * |G2 (r ^ 2)| * ((‖h‖ * ‖ν‖) * (r * ‖e‖) + (r * ‖ν‖) * (‖h‖ * ‖e‖)) := by gcongr
        _ = 8 * (|G2 (r ^ 2)| * r) * (‖ν‖ * ‖e‖) * ‖h‖ := by ring
        _ ≤ 8 * (M2 / (d / 2)) * (‖ν‖ * ‖e‖) * ‖h‖ := by gcongr
    · rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      calc 4 * |G2 (‖x - z‖ ^ 2)| * |@inner ℝ R2 _ (x - z) h| * |@inner ℝ R2 _ ν e|
          ≤ 4 * |G2 (r ^ 2)| * (r * ‖h‖) * (‖ν‖ * ‖e‖) := by gcongr
        _ = 4 * (|G2 (r ^ 2)| * r) * (‖ν‖ * ‖e‖) * ‖h‖ := by ring
        _ ≤ 4 * (M2 / (d / 2)) * (‖ν‖ * ‖e‖) * ‖h‖ := by gcongr



/-- higher radial derivatives from the Bessel ODE, with weighted bounds -/
lemma profile_higher (G G1 : ℝ → ℝ) (A : ℝ) (hA : 0 < A) (t0 : ℝ) (ht0 : 0 < t0)
    (hG : ∀ t, 0 < t → HasDerivAt G (G1 t) t) (hG1 : ∀ t, 0 < t → DifferentiableAt ℝ G1 t)
    (hode : ∀ t, 0 < t → HasDerivAt (fun t => t * G1 t) (-A * G t) t) :
    ∃ M1 M2 M3 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧ 0 ≤ M3 ∧
      (∀ t, 0 < t → HasDerivAt G1 ((-A * G t - G1 t) / t) t) ∧
      (∀ t, 0 < t → HasDerivAt (fun t => (-A * G t - G1 t) / t)
        ((-A * G1 t - 2 * ((-A * G t - G1 t) / t)) / t) t) ∧
      (∀ t, t0 ≤ t → |G1 t| * Real.sqrt t ≤ M1) ∧
      (∀ t, t0 ≤ t → |(-A * G t - G1 t) / t| * t ≤ M2) ∧
      (∀ t, t0 ≤ t → |(-A * G1 t - 2 * ((-A * G t - G1 t) / t)) / t| * (t * Real.sqrt t) ≤ M3) := by
  obtain ⟨M, hM⟩ := energy_bound G G1 A hA t0 ht0 hG hG1 hode
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t0 le_rfl).1
  have hs0 : 0 < Real.sqrt t0 := Real.sqrt_pos.mpr ht0
  have hD1 : ∀ t, 0 < t → HasDerivAt G1 ((-A * G t - G1 t) / t) t := by
    intro t ht
    have hg := (hG1 t ht).hasDerivAt
    have hrel : -A * G t = G1 t + t * deriv G1 t := by
      have := (hasDerivAt_id t).mul hg
      simp only [id, one_mul] at this
      exact (hode t ht).unique this
    refine hg.congr_deriv ?_
    field_simp
    linarith
  set M2 := A * M + M / Real.sqrt t0
  refine ⟨M, M2, A * M + 2 * (M2 / Real.sqrt t0), hM0, by positivity, by positivity, hD1, ?_,
    fun t ht => (hM t ht).2, ?_, ?_⟩
  · intro t ht
    have h := (((hG t ht).const_mul (-A)).sub (hD1 t ht)).div (hasDerivAt_id t) ht.ne'
    refine h.congr_deriv ?_
    simp only [id, Pi.sub_apply]
    field_simp
    ring
  · intro t ht
    have htp : 0 < t := lt_of_lt_of_le ht0 ht
    obtain ⟨h1, h2⟩ := hM t ht
    have hst : Real.sqrt t0 ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
    have hG1b : |G1 t| ≤ M / Real.sqrt t0 := by
      rw [le_div_iff₀ hs0]
      exact (mul_le_mul_of_nonneg_left hst (abs_nonneg _)).trans h2
    rw [abs_div, abs_of_pos htp, div_mul_cancel₀ _ htp.ne']
    calc |-A * G t - G1 t| ≤ A * |G t| + |G1 t| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_neg, abs_of_pos hA]
      _ ≤ A * M + M / Real.sqrt t0 := by gcongr
  · intro t ht
    have htp : 0 < t := lt_of_lt_of_le ht0 ht
    obtain ⟨h1, h2⟩ := hM t ht
    have hst : Real.sqrt t0 ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
    have hsp : 0 < Real.sqrt t := Real.sqrt_pos.mpr htp
    have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htp.le
    have hG1b : |G1 t| ≤ M / Real.sqrt t0 := by
      rw [le_div_iff₀ hs0]
      exact (mul_le_mul_of_nonneg_left hst (abs_nonneg _)).trans h2
    have hG2t : |(-A * G t - G1 t) / t| * t ≤ M2 := by
      rw [abs_div, abs_of_pos htp, div_mul_cancel₀ _ htp.ne']
      calc |-A * G t - G1 t| ≤ A * |G t| + |G1 t| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_neg, abs_of_pos hA]
        _ ≤ A * M + M / Real.sqrt t0 := by gcongr
    have hG2s : |(-A * G t - G1 t) / t| * Real.sqrt t ≤ M2 / Real.sqrt t0 := by
      rw [le_div_iff₀ hs0]
      calc |(-A * G t - G1 t) / t| * Real.sqrt t * Real.sqrt t0 ≤
          |(-A * G t - G1 t) / t| * Real.sqrt t * Real.sqrt t := by gcongr
        _ = |(-A * G t - G1 t) / t| * t := by rw [mul_assoc, hss]
        _ ≤ M2 := hG2t
    rw [abs_div, abs_of_pos htp]
    calc |-A * G1 t - 2 * ((-A * G t - G1 t) / t)| / t * (t * Real.sqrt t)
        = |-A * G1 t - 2 * ((-A * G t - G1 t) / t)| * Real.sqrt t := by field_simp
      _ ≤ (A * |G1 t| + 2 * |(-A * G t - G1 t) / t|) * Real.sqrt t := by
          gcongr
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos hA, abs_two]
      _ = A * (|G1 t| * Real.sqrt t) + 2 * (|(-A * G t - G1 t) / t| * Real.sqrt t) := by ring
      _ ≤ A * M + 2 * (M2 / Real.sqrt t0) := by gcongr



lemma gamma_holder' (f : ℝ → ℝ) (hfc : Continuous f) (z : R2) (d : ℝ) (hd : 0 < d)
    (hΓ : ∀ s, d ≤ ‖gpt f s - z‖) (u : R2 → ℝ) (B K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ x, d / 2 < ‖x - z‖ → |u x| ≤ B ∧ ∃ L : R2 →L[ℝ] ℝ, HasFDerivAt u L x ∧ ‖L‖ ≤ K) :
    IsBC0AlphaGam f (1 / 2) (fun s => ((u (gpt f s) : ℝ) : ℂ)) := by
  classical
  let L : R2 → (R2 →L[ℝ] ℝ) := fun x =>
    if h : d / 2 < ‖x - z‖ then ((hu x h).2).choose else 0
  refine gamma_holder f hfc z d hd hΓ u L B K hK fun x hx => ?_
  have e : L x = ((hu x hx).2).choose := by simp [L, hx]
  rw [e]
  exact ⟨((hu x hx).2).choose_spec.1, ((hu x hx).2).choose_spec.2, (hu x hx).1⟩

lemma holder_const (f : ℝ → ℝ) (α : ℝ) (c : ℂ) : IsBC0AlphaGam f α (fun _ => c) :=
  ⟨continuous_const, ⟨‖c‖, fun _ => le_rfl⟩, 0, fun s t => by simp⟩

lemma holder_vec2 (f : ℝ → ℝ) (α : ℝ) {a b : ℝ → ℂ} (ha : IsBC0AlphaGam f α a)
    (hb : IsBC0AlphaGam f α b) :
    IsBC0AlphaGam f α (fun s => (!₂[a s, b s] : EuclideanSpace ℂ (Fin 2))) := by
  obtain ⟨hc1, ⟨B1, hB1⟩, H1, hH1⟩ := ha
  obtain ⟨hc2, ⟨B2, hB2⟩, H2, hH2⟩ := hb
  have hnorm : ∀ x y : ℂ, ‖(!₂[x, y] : EuclideanSpace ℂ (Fin 2))‖ ≤ ‖x‖ + ‖y‖ := by
    intro x y
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, PiLp.toLp_apply]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg x, norm_nonneg y]
  refine ⟨?_, ⟨B1 + B2, fun s => (hnorm _ _).trans (add_le_add (hB1 s) (hB2 s))⟩, H1 + H2,
    fun s t => ?_⟩
  · have : Continuous fun s => (WithLp.toLp 2 ![a s, b s] : EuclideanSpace ℂ (Fin 2)) := by
      refine (PiLp.continuous_toLp 2 _).comp ?_
      refine continuous_pi fun i => ?_
      fin_cases i <;> simpa
    exact this
  · have e : (!₂[a s, b s] : EuclideanSpace ℂ (Fin 2)) - !₂[a t, b t] = !₂[a s - a t, b s - b t] := by
      ext i; fin_cases i <;> simp
    rw [e]
    refine (hnorm _ _).trans ?_
    linarith [hH1 s t, hH2 s t]

lemma inv_sq_lip (a b : ℝ) : |(1 + a ^ 2)⁻¹ - (1 + b ^ 2)⁻¹| ≤ 2 * |a - b| := by
  have ha : 0 < 1 + a ^ 2 := by positivity
  have hb : 0 < 1 + b ^ 2 := by positivity
  rw [inv_sub_inv ha.ne' hb.ne', abs_div, abs_of_pos (mul_pos ha hb),
    div_le_iff₀ (mul_pos ha hb)]
  have e : 1 + b ^ 2 - (1 + a ^ 2) = (b - a) * (b + a) := by ring
  rw [e, abs_mul, abs_sub_comm]
  have h1 : |b + a| ≤ 2 * ((1 + a ^ 2) * (1 + b ^ 2)) := by
    have := abs_add_le b a
    have hb' : |b| ≤ 1 + b ^ 2 := by nlinarith [abs_nonneg b, sq_abs b]
    have ha' : |a| ≤ 1 + a ^ 2 := by nlinarith [abs_nonneg a, sq_abs a]
    nlinarith [mul_pos ha hb]
  have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (a - b))
  linarith

lemma inv_sqrt_lip (a b : ℝ) :
    |(Real.sqrt (1 + a ^ 2))⁻¹ - (Real.sqrt (1 + b ^ 2))⁻¹| ≤ |a - b| := by
  set p := Real.sqrt (1 + a ^ 2)
  set q := Real.sqrt (1 + b ^ 2)
  have hp1 : 1 ≤ p := by rw [Real.one_le_sqrt]; nlinarith [sq_nonneg a]
  have hq1 : 1 ≤ q := by rw [Real.one_le_sqrt]; nlinarith [sq_nonneg b]
  have hp2 : p ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hq2 : q ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hpa : |a| ≤ p := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hqb : |b| ≤ q := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  rw [inv_sub_inv hp0.ne' hq0.ne', abs_div, abs_of_pos (mul_pos hp0 hq0),
    div_le_iff₀ (mul_pos hp0 hq0)]
  have hqp : (q - p) * (q + p) = (b - a) * (b + a) := by nlinarith
  have hsum : |b + a| ≤ q + p := (abs_add_le b a).trans (by linarith)
  have hqp' : |q - p| * (q + p) = |a - b| * |b + a| := by
    rw [← abs_of_pos (by linarith : (0:ℝ) < q + p), ← abs_mul, hqp, abs_mul,
      abs_sub_comm b a]
  have h1 : |q - p| ≤ |a - b| := by
    have := mul_le_mul_of_nonneg_left hsum (abs_nonneg (a - b))
    by_contra hc; push Not at hc
    have := mul_lt_mul_of_pos_right hc (by linarith : (0:ℝ) < q + p)
    linarith
  have := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hp1 hq1) (abs_nonneg (a - b))
  linarith



noncomputable def βk (k : ℝ) : ℂ := Complex.I / 4 -
  (((Real.log (k / 2) + Real.eulerMascheroniConstant) / (2 * Real.pi) : ℝ) : ℂ)

lemma phi_loc (k : ℝ) (hk : 0 < k) (z y : R2) (hy : y ≠ z) :
    Phi k y z = ((Rt (k ^ 2 / 4) (‖y - z‖ ^ 2) : ℝ) : ℂ) +
      βk k * ((Jt (k ^ 2 / 4) (‖y - z‖ ^ 2) : ℝ) : ℂ) := by
  rw [phi_decomp k hk y z hy, aF_eq, phi0_eq]
  simp only [bF, Rt, Jt, ell, βk]
  have htq : tq k (y - z) = k ^ 2 / 4 * ‖y - z‖ ^ 2 := by unfold tq; ring
  rw [htq, ← Qs_eq]
  push_cast
  ring

/-- the dipole as a combination of two real radial dipoles -/
lemma dipole_loc (k : ℝ) (hk : 0 < k) (z ν x : R2) (hx : x ≠ z) :
    dipoleSource k z ν x = ((pD (R1t (k ^ 2 / 4)) z ν x : ℝ) : ℂ) +
      βk k * ((pD (J1t (k ^ 2 / 4)) z ν x : ℝ) : ℂ) := by
  set A := k ^ 2 / 4
  have hloc : (fun y => Phi k y z) =ᶠ[𝓝 x]
      fun y => ((Rt A (‖y - z‖ ^ 2) : ℝ) : ℂ) + βk k * ((Jt A (‖y - z‖ ^ 2) : ℝ) : ℂ) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact phi_loc k hk z y hy
  have hN0 : 0 < ‖x - z‖ ^ 2 := by
    have : x - z ≠ 0 := sub_ne_zero.mpr hx
    positivity
  have hR := (hasDerivAt_Rt A _ hN0.ne').comp_hasFDerivAt x (hasFDerivAt_N z x)
  have hJ := (hasDerivAt_Jt A (‖x - z‖ ^ 2)).comp_hasFDerivAt x (hasFDerivAt_N z x)
  have hs := (Complex.ofRealCLM.hasFDerivAt.comp x hR).add
    ((Complex.ofRealCLM.hasFDerivAt.comp x hJ).const_mul (βk k))
  unfold dipoleSource
  rw [hloc.fderiv_eq, HasFDerivAt.fderiv (f := fun y => ((Rt A (‖y - z‖ ^ 2) : ℝ) : ℂ) +
    βk k * ((Jt A (‖y - z‖ ^ 2) : ℝ) : ℂ)) hs]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, nsmul_eq_mul,
    innerSL_apply_apply, Nat.cast_ofNat, pD, Function.comp_def]
  push_cast
  ring

/-- derivative of the dipole away from `z` -/
lemma dipole_hasFDerivAt (k : ℝ) (hk : 0 < k) (z ν x : R2) (hx : x ≠ z) :
    ∃ D : R2 →L[ℝ] ℂ, HasFDerivAt (dipoleSource k z ν) D x ∧ ∀ e, D e =
      ((vD (R1t (k ^ 2 / 4)) (fun t => (-(k ^ 2 / 4) * Rt (k ^ 2 / 4) t - R1t (k ^ 2 / 4) t) / t)
        z ν e x : ℝ) : ℂ) +
      βk k * ((vD (J1t (k ^ 2 / 4)) (fun t => (-(k ^ 2 / 4) * Jt (k ^ 2 / 4) t - J1t (k ^ 2 / 4) t) / t)
        z ν e x : ℝ) : ℂ) := by
  set A := k ^ 2 / 4
  have hA : 0 < A := by positivity
  obtain ⟨-, -, -, -, -, -, hR2, -, -, -, -⟩ := profile_higher (Rt A) (R1t A) A hA 1 one_pos
    (fun t ht => hasDerivAt_Rt A t ht.ne') (fun t ht => R1t_diff A t ht) (fun t ht => ode_Rt A t ht)
  obtain ⟨-, -, -, -, -, -, hJ2, -, -, -, -⟩ := profile_higher (Jt A) (J1t A) A hA 1 one_pos
    (fun t _ => hasDerivAt_Jt A t) (fun t _ => J1t_diff A t) (fun t _ => ode_Jt A t)
  obtain ⟨LR, hLR, hLRe⟩ := pD_hasFDerivAt (R1t A) _ z ν hR2 x hx
  obtain ⟨LJ, hLJ, hLJe⟩ := pD_hasFDerivAt (J1t A) _ z ν hJ2 x hx
  have hs := (Complex.ofRealCLM.hasFDerivAt.comp x hLR).add
    ((Complex.ofRealCLM.hasFDerivAt.comp x hLJ).const_mul (βk k))
  have hev : dipoleSource k z ν =ᶠ[𝓝 x] fun y => ((pD (R1t A) z ν y : ℝ) : ℂ) +
      βk k * ((pD (J1t A) z ν y : ℝ) : ℂ) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact dipole_loc k hk z ν y hy
  refine ⟨_, hs.congr_of_eventuallyEq hev, fun e => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, hLRe, hLJe]



noncomputable abbrev E0 : R2 := EuclideanSpace.single 0 1
noncomputable abbrev E1 : R2 := EuclideanSpace.single 1 1

lemma pt_eq (a b : ℝ) : pt a b = a • E0 + b • E1 := by
  ext i; fin_cases i <;> simp [pt]

lemma hasDerivAt_gpt (f : ℝ → ℝ) (hf : Differentiable ℝ f) (s : ℝ) :
    HasDerivAt (gpt f) (pt 1 (deriv f s)) s := by
  have h := ((hasDerivAt_id s).smul_const E0).add ((hf s).hasDerivAt.smul_const E1)
  have e : gpt f = fun s => id s • E0 + f s • E1 := by
    funext s; rw [gpt, pt_eq]; rfl
  rw [e, pt_eq]; exact h

theorem ddh (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (k : ℝ) (hk : 0 < k)
    (z : R2) (hz : z ∈ Dplus f) (ν : R2) :
    IsBC1AlphaGam f (1 / 2) (incData f (dipoleSource k z ν)).1 ∧
      IsBC0AlphaGam f (1 / 2) (incData f (dipoleSource k z ν)).2 := by
  have hfc : Continuous f := hf.1.continuous
  -- distance from the source to `Γ`
  set S : Set R2 := {x | x 1 ≤ f (x 0)}
  have hSc : IsClosed S := isClosed_le (by fun_prop) (hfc.comp (by fun_prop))
  have hzS : z ∉ S := fun h => by
    simp only [S, Dplus, Set.mem_setOf_eq] at h hz; linarith
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hSc.isOpen_compl z hzS
  have hΓ : ∀ s, d ≤ ‖gpt f s - z‖ := by
    intro s; by_contra h; push Not at h
    have : gpt f s ∈ S := by simp [S, gpt, pt]
    exact hball (by rw [mem_ball, dist_eq_norm]; exact h) this
  have hne : ∀ s, gpt f s ≠ z := fun s h => by
    have := hΓ s; rw [h, sub_self, norm_zero] at this; linarith
  set A := k ^ 2 / 4
  have hA : 0 < A := by positivity
  set t0 := (d / 2) ^ 2
  have ht0 : 0 < t0 := by positivity
  obtain ⟨M1R, M2R, M3R, hM1R, hM2R, hM3R, hR1, hR2, B1R, B2R, B3R⟩ :=
    profile_higher (Rt A) (R1t A) A hA t0 ht0 (fun t ht => hasDerivAt_Rt A t ht.ne')
      (fun t ht => R1t_diff A t ht) (fun t ht => ode_Rt A t ht)
  obtain ⟨M1J, M2J, M3J, hM1J, hM2J, hM3J, hJ1, hJ2, B1J, B2J, B3J⟩ :=
    profile_higher (Jt A) (J1t A) A hA t0 ht0 (fun t _ => hasDerivAt_Jt A t)
      (fun t _ => J1t_diff A t) (fun t _ => ode_Jt A t)
  have bR := fun e => radial_dipole_bounds _ _ _ z ν e d hd M1R M2R M3R hM1R hM2R hM3R hR1 hR2 B1R B2R B3R
  have bJ := fun e => radial_dipole_bounds _ _ _ z ν e d hd M1J M2J M3J hM1J hM2J hM3J hJ1 hJ2 B1J B2J B3J
  set β := βk k
  -- Hölder pieces
  have hvD : ∀ (e : R2) (G1 G2 : ℝ → ℝ) (M1 M2 M3 : ℝ),
      (∀ x, d / 2 < ‖x - z‖ → |pD G1 z ν x| ≤ 2 * M1 * ‖ν‖ ∧
        |vD G1 G2 z ν e x| ≤ (4 * M2 + 2 * M1 / (d / 2)) * (‖ν‖ * ‖e‖) ∧
        ∃ L : R2 →L[ℝ] ℝ, HasFDerivAt (vD G1 G2 z ν e) L x ∧
          ‖L‖ ≤ (8 * M3 + 12 * M2 / (d / 2)) * (‖ν‖ * ‖e‖)) → 0 ≤ M2 → 0 ≤ M3 →
      IsBC0AlphaGam f (1 / 2) (fun s => ((vD G1 G2 z ν e (gpt f s) : ℝ) : ℂ)) := by
    intro e G1 G2 M1 M2 M3 hb hM2 hM3
    exact gamma_holder' f hfc z d hd hΓ _ _ _ (by positivity) fun x hx =>
      ⟨(hb x hx).2.1, (hb x hx).2.2⟩
  set Dd : R2 → ℝ → ℂ := fun e s =>
    ((vD (R1t A) (fun t => (-A * Rt A t - R1t A t) / t) z ν e (gpt f s) : ℝ) : ℂ) +
      β * ((vD (J1t A) (fun t => (-A * Jt A t - J1t A t) / t) z ν e (gpt f s) : ℝ) : ℂ)
  have hDd : ∀ e : R2, IsBC0AlphaGam f (1 / 2) (Dd e) := fun e =>
    IsBC0AlphaGam.add f _ (hvD e _ _ _ _ _ (bR e) hM2R hM3R)
      (IsBC0AlphaGam.mul f _ (holder_const f _ β) (hvD e _ _ _ _ _ (bJ e) hM2J hM3J))
  obtain ⟨Cd, hCd⟩ := hf.2.2.2.1
  obtain ⟨Cl, hCl⟩ := hf.2.2.2.2
  have hlip : ∀ s t, |deriv f s - deriv f t| ≤ max Cl 0 * ‖gpt f s - gpt f t‖ := by
    intro s t
    have := hCl s t
    rw [Real.rpow_one] at this
    calc _ ≤ Cl * |s - t| := this
      _ ≤ max Cl 0 * |s - t| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      _ ≤ max Cl 0 * ‖gpt f s - gpt f t‖ :=
          mul_le_mul_of_nonneg_left (abs_sub_le_gpt f s t) (le_max_right _ _)
  have hFd : IsBC0AlphaGam f (1 / 2) (fun s => ((deriv f s : ℝ) : ℂ)) := by
    refine holder_of_lip f _ (Complex.continuous_ofReal.comp hf.2.1) Cd
      (fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hCd s) 1 (max Cl 0) one_pos
      (le_max_right _ _) fun s t _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hlip s t
  have hcinv : IsBC0AlphaGam f (1 / 2) (fun s => (((1 + deriv f s ^ 2)⁻¹ : ℝ) : ℂ)) := by
    refine holder_of_lip f _ ?_ 1 (fun s => ?_) 1 (2 * max Cl 0) one_pos (mul_nonneg zero_le_two (le_max_right _ _))
      fun s t _ => ?_
    · exact Complex.continuous_ofReal.comp ((continuous_const.add (hf.2.1.pow 2)).inv₀
        fun s => (by positivity : (0:ℝ) < 1 + deriv f s ^ 2).ne')
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (deriv f s)])
    · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      refine (inv_sq_lip _ _).trans ?_
      have := hlip s t
      linarith
  have hq : IsBC0AlphaGam f (1 / 2) (fun s => (((arcDen f s)⁻¹ : ℝ) : ℂ)) := by
    refine holder_of_lip f _ ?_ 1 (fun s => ?_) 1 (max Cl 0) one_pos (le_max_right _ _)
      fun s t _ => ?_
    · refine Complex.continuous_ofReal.comp (Continuous.inv₀ ?_ fun s => ?_)
      · unfold arcDen; exact (continuous_const.add (hf.2.1.pow 2)).sqrt
      · exact (Real.sqrt_pos.mpr (by positivity)).ne'
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
        (show 0 < arcDen f s from Real.sqrt_pos.mpr (by positivity)))]
      exact inv_le_one_of_one_le₀ (by rw [arcDen, Real.one_le_sqrt]; nlinarith [sq_nonneg (deriv f s)])
    · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact (inv_sqrt_lip _ _).trans (hlip s t)
  -- the dipole and its derivative on `Γ`
  have hD : ∀ s, ∃ D : R2 →L[ℝ] ℂ, HasFDerivAt (dipoleSource k z ν) D (gpt f s) ∧
      ∀ e, D e = Dd e s := fun s => dipole_hasFDerivAt k hk z ν (gpt f s) (hne s)
  choose D hDd' hDe using hD
  have hlinD : ∀ s (a b : ℝ), D s (pt a b) = (a : ℂ) * Dd E0 s + (b : ℂ) * Dd E1 s := by
    intro s a b
    rw [pt_eq, map_add, map_smul, map_smul, hDe, hDe, Complex.real_smul, Complex.real_smul]
  have hg1d : ∀ s, HasDerivAt (incData f (dipoleSource k z ν)).1
      (-(Dd E0 s + ((deriv f s : ℝ) : ℂ) * Dd E1 s)) s := by
    intro s
    have h := ((hDd' s).comp_hasDerivAt s (hasDerivAt_gpt f hf.1 s)).neg
    refine h.congr_deriv ?_
    rw [hlinD]; push_cast; ring
  -- `g₁` itself
  have hpD : IsBC0AlphaGam f (1 / 2) (incData f (dipoleSource k z ν)).1 := by
    have hR : IsBC0AlphaGam f (1 / 2) (fun s => ((pD (R1t A) z ν (gpt f s) : ℝ) : ℂ)) := by
      refine gamma_holder' f hfc z d hd hΓ _ _ ((4 * M2R + 2 * M1R / (d / 2)) * ‖ν‖)
        (by positivity) fun x hx => ⟨(bR E0 x hx).1, ?_⟩
      have hxz : x ≠ z := fun h => by rw [h, sub_self, norm_zero] at hx; linarith
      obtain ⟨L, hL, hLe⟩ := pD_hasFDerivAt (R1t A) _ z ν hR1 x hxz
      refine ⟨L, hL, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_⟩
      rw [hLe, Real.norm_eq_abs]
      have := (bR h x hx).2.1
      calc _ ≤ _ := this
        _ = _ := by ring
    have hJ : IsBC0AlphaGam f (1 / 2) (fun s => ((pD (J1t A) z ν (gpt f s) : ℝ) : ℂ)) := by
      refine gamma_holder' f hfc z d hd hΓ _ _ ((4 * M2J + 2 * M1J / (d / 2)) * ‖ν‖)
        (by positivity) fun x hx => ⟨(bJ E0 x hx).1, ?_⟩
      have hxz : x ≠ z := fun h => by rw [h, sub_self, norm_zero] at hx; linarith
      obtain ⟨L, hL, hLe⟩ := pD_hasFDerivAt (J1t A) _ z ν hJ1 x hxz
      refine ⟨L, hL, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_⟩
      rw [hLe, Real.norm_eq_abs]
      have := (bJ h x hx).2.1
      calc _ ≤ _ := this
        _ = _ := by ring
    have h := IsBC0AlphaGam.neg f _
      (IsBC0AlphaGam.add f _ hR (IsBC0AlphaGam.mul f _ (holder_const f _ β) hJ))
    have e : (incData f (dipoleSource k z ν)).1 = fun s =>
        -(((pD (R1t A) z ν (gpt f s) : ℝ) : ℂ) + β * ((pD (J1t A) z ν (gpt f s) : ℝ) : ℂ)) := by
      funext s; simp only [incData]; rw [dipole_loc k hk z ν (gpt f s) (hne s)]
    rw [e]; exact h
  refine ⟨⟨⟨hpD.1, hpD.2.1⟩, fun s => (hg1d s).differentiableAt, ?_⟩, ?_⟩
  · -- surface gradient
    have e : surfGrad f (incData f (dipoleSource k z ν)).1 = fun s =>
        (!₂[(-(Dd E0 s + ((deriv f s : ℝ) : ℂ) * Dd E1 s)) * (((1 + deriv f s ^ 2)⁻¹ : ℝ) : ℂ),
          (-(Dd E0 s + ((deriv f s : ℝ) : ℂ) * Dd E1 s)) * ((deriv f s : ℝ) : ℂ) *
            (((1 + deriv f s ^ 2)⁻¹ : ℝ) : ℂ)] : EuclideanSpace ℂ (Fin 2)) := by
      funext s
      simp only [surfGrad, (hg1d s).deriv]
      push_cast
      simp only [div_eq_mul_inv]
    rw [e]
    have hbase := IsBC0AlphaGam.neg f _
      (IsBC0AlphaGam.add f _ (hDd E0) (IsBC0AlphaGam.mul f _ hFd (hDd E1)))
    exact holder_vec2 f _ (IsBC0AlphaGam.mul f _ hbase hcinv)
      (IsBC0AlphaGam.mul f _ (IsBC0AlphaGam.mul f _ hbase hFd) hcinv)
  · -- `g₂`
    have e : (incData f (dipoleSource k z ν)).2 = fun s =>
        -((((arcDen f s)⁻¹ : ℝ) : ℂ) * ((deriv f s : ℝ) : ℂ) * Dd E0 s +
          (-(((arcDen f s)⁻¹ : ℝ) : ℂ)) * Dd E1 s) := by
      funext s
      simp only [incData]
      rw [(hDd' s).fderiv, normal, map_smul, hlinD, Complex.real_smul]
      push_cast
      ring
    rw [e]
    exact IsBC0AlphaGam.neg f _ (IsBC0AlphaGam.add f _
      (IsBC0AlphaGam.mul f _ (IsBC0AlphaGam.mul f _ hq hFd) (hDd E0))
      (IsBC0AlphaGam.mul f _ (IsBC0AlphaGam.neg f _ hq) (hDd E1)))



/-- Radial estimate: integrating `K (1 + |w|^(α-1))` along the ray from `0` to `a`. -/
lemma radial_holder (g : R2 → ℂ) (hc : Continuous g) (K α : ℝ) (hα0 : 0 < α) (hK : 0 ≤ K)
    (hd : ∀ w : R2, w ≠ 0 → ∃ L : R2 →L[ℝ] ℂ, HasFDerivAt g L w ∧ ‖L‖ ≤ K * (1 + ‖w‖ ^ (α - 1)))
    (a : R2) : ‖g a - g 0‖ ≤ K * (‖a‖ + ‖a‖ ^ α / α) := by
  by_cases ha : a = 0
  · subst ha; simp; positivity
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set Kb : ℝ → ℝ := fun τ => K * (τ * ‖a‖ + ‖a‖ ^ α * τ ^ α / α) with hKb
  -- estimate on `[ε, 1]`
  have hstep : ∀ ε : ℝ, 0 < ε → ε < 1 → ‖g a - g (ε • a)‖ ≤ Kb 1 := by
    intro ε hε hε1
    have hderiv : ∀ τ ∈ Set.Icc ε 1, ∃ L : R2 →L[ℝ] ℂ, HasFDerivAt g L (τ • a) ∧
        ‖L‖ ≤ K * (1 + ‖τ • a‖ ^ (α - 1)) := fun τ hτ =>
      hd _ (smul_ne_zero (by linarith [hτ.1]) ha)
    choose! L hL hLb using hderiv
    have hF := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      (f := fun τ => g (τ • a) - g (ε • a)) (f' := fun τ => L τ a) (a := ε) (b := 1)
      (B := fun τ => Kb τ - Kb ε) (B' := fun τ => K * (‖a‖ + ‖a‖ ^ α * τ ^ (α - 1)))
      ((hc.comp ((continuous_id (X := ℝ)).smul (continuous_const (y := a)))).sub
        continuous_const).continuousOn
      (fun τ hτ => by
        have hτ' : τ ∈ Set.Icc ε 1 := ⟨hτ.1, hτ.2.le⟩
        have h := (hL τ hτ').comp_hasDerivAt τ ((hasDerivAt_id τ).smul_const a)
        simpa using (h.sub_const (g (ε • a))).hasDerivWithinAt)
      (by simp)
      (by
        simp only [hKb]
        refine ContinuousOn.sub ?_ continuousOn_const
        refine continuousOn_const.mul ((continuousOn_id.mul continuousOn_const).add
          ((continuousOn_const.mul ?_).div_const α))
        exact fun τ hτ => (Real.continuousAt_rpow_const τ α (Or.inr hα0.le)).continuousWithinAt)
      (fun τ hτ => by
        have hτ0 : 0 < τ := lt_of_lt_of_le hε hτ.1
        have h1 := ((hasDerivAt_id τ).mul_const ‖a‖).add
          (((Real.hasDerivAt_rpow_const (p := α) (Or.inl hτ0.ne')).const_mul (‖a‖ ^ α)).div_const α)
        have h2 := (h1.const_mul K).sub_const (Kb ε)
        refine (h2.congr_deriv ?_).hasDerivWithinAt
        field_simp)
      (fun τ hτ => by
        have hτ0 : 0 < τ := lt_of_lt_of_le hε hτ.1
        have hτ' : τ ∈ Set.Icc ε 1 := ⟨hτ.1, hτ.2.le⟩
        refine ((L τ).le_opNorm a).trans ?_
        have hb := hLb τ hτ'
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0] at hb
        rw [Real.mul_rpow hτ0.le hna.le] at hb
        calc ‖L τ‖ * ‖a‖ ≤ K * (1 + τ ^ (α - 1) * ‖a‖ ^ (α - 1)) * ‖a‖ := by gcongr
          _ = K * (‖a‖ + ‖a‖ ^ α * τ ^ (α - 1)) := by
              rw [show ‖a‖ ^ α = ‖a‖ ^ (α - 1) * ‖a‖ by
                rw [← Real.rpow_add_one hna.ne']; ring_nf]
              ring)
    have h1 := hF (x := 1) ⟨hε1.le, le_rfl⟩
    simp only [one_smul] at h1
    have hKe : 0 ≤ Kb ε := by simp only [hKb]; positivity
    linarith
  -- let `ε → 0`
  have hlim : Tendsto (fun ε : ℝ => ‖g a - g (ε • a)‖) (𝓝[>] 0) (𝓝 ‖g a - g 0‖) := by
    have : Tendsto (fun ε : ℝ => g (ε • a)) (𝓝[>] 0) (𝓝 (g 0)) := by
      have hcont : Continuous fun ε : ℝ => g (ε • a) := hc.comp (continuous_id.smul continuous_const)
      have h := hcont.tendsto (0 : ℝ)
      rw [zero_smul] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact (tendsto_const_nhds.sub this).norm
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖g a - g (ε • a)‖ ≤ Kb 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    exact hstep ε hε.1 hε.2
  have := le_of_tendsto hlim hev
  simpa [hKb] using this

lemma sing_holder (g : R2 → ℂ) (hc : Continuous g) (B K α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hK : 0 ≤ K) (hB : ∀ x, ‖g x‖ ≤ B)
    (hd : ∀ w : R2, w ≠ 0 → ∃ L : R2 →L[ℝ] ℂ, HasFDerivAt g L w ∧ ‖L‖ ≤ K * (1 + ‖w‖ ^ (α - 1))) :
    ∀ a b : R2, ‖g a - g b‖ ≤ (2 * B + 2 * K + 4 * K * (1 + 1 / α)) * ‖a - b‖ ^ α := by
  intro a b
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set ρ := ‖a - b‖ with hρ
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hHnn : 0 ≤ 4 * K * (1 + 1 / α) := by positivity
  rcases eq_or_lt_of_le hρ0 with h0 | hpos
  · have : a = b := by rw [← sub_eq_zero, ← norm_eq_zero]; exact h0.symm
    subst this; simp only [sub_self, norm_zero]; positivity
  have hρa : 0 < ρ ^ α := Real.rpow_pos_of_pos hpos α
  rcases le_or_gt 1 ρ with h1 | h1
  · -- far apart
    have hr1 : 1 ≤ ρ ^ α := Real.one_le_rpow h1 hα0.le
    have := norm_sub_le (g a) (g b)
    nlinarith [hB a, hB b, mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ 2 * K),
      mul_le_mul_of_nonneg_left hr1 hHnn]
  have hρle : ρ ≤ ρ ^ α := by
    calc ρ = ρ ^ (1 : ℝ) := (Real.rpow_one ρ).symm
      _ ≤ ρ ^ α := Real.rpow_le_rpow_of_exponent_ge hpos h1.le hα1.le
  by_cases hfar : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ρ ≤ ‖a + τ • (b - a)‖
  · -- the segment stays away from the singularity
    have hseg : ∀ p ∈ segment ℝ a b, ρ ≤ ‖p‖ := by
      intro p hp
      rw [segment_eq_image'] at hp
      obtain ⟨τ, hτ, rfl⟩ := hp
      exact hfar τ hτ
    have hderiv : ∀ p ∈ segment ℝ a b, ∃ L : R2 →L[ℝ] ℂ, HasFDerivAt g L p ∧
        ‖L‖ ≤ K * (1 + ρ ^ (α - 1)) := by
      intro p hp
      have hp0 : p ≠ 0 := fun h => by
        have := hseg p hp; rw [h, norm_zero] at this; linarith
      obtain ⟨L, hL, hLb⟩ := hd p hp0
      refine ⟨L, hL, hLb.trans ?_⟩
      exact mul_le_mul_of_nonneg_left (add_le_add_right
        (Real.rpow_le_rpow_of_nonpos hpos (hseg p hp) (sub_nonpos.mpr hα1.le)) 1) hK
    choose! L hL hLb using hderiv
    have hmv := (convex_segment a b).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := g) (f' := L) (fun p hp => (hL p hp).hasFDerivWithinAt) hLb
      (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
    rw [norm_sub_rev (g b), norm_sub_rev b a, ← hρ] at hmv
    have e : K * (1 + ρ ^ (α - 1)) * ρ = K * (ρ + ρ ^ α) := by
      rw [show ρ ^ α = ρ ^ (α - 1) * ρ by rw [← Real.rpow_add_one hpos.ne']; ring_nf]
      ring
    rw [e] at hmv
    have : K * (ρ + ρ ^ α) ≤ 2 * K * ρ ^ α := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hρa.le (by positivity : 0 ≤ 2 * B),
      mul_le_mul_of_nonneg_left hρa.le hHnn]
  · -- both points are close to the singularity
    push Not at hfar
    obtain ⟨τ, hτ, hτρ⟩ := hfar
    have hpa : ‖a + τ • (b - a) - a‖ ≤ ρ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1, norm_sub_rev, ← hρ]
      calc τ * ρ ≤ 1 * ρ := by gcongr; exact hτ.2
        _ = ρ := one_mul ρ
    have hpb : ‖a + τ • (b - a) - b‖ ≤ ρ := by
      have e : a + τ • (b - a) - b = (1 - τ) • (a - b) := by
        module
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hτ.2]), ← hρ]
      calc (1 - τ) * ρ ≤ 1 * ρ := by gcongr; linarith [hτ.1]
        _ = ρ := one_mul ρ
    have hna : ‖a‖ ≤ 2 * ρ := by
      have := norm_sub_le (a + τ • (b - a)) (a + τ • (b - a) - a)
      rw [sub_sub_cancel] at this
      linarith
    have hnb : ‖b‖ ≤ 2 * ρ := by
      have := norm_sub_le (a + τ • (b - a)) (a + τ • (b - a) - b)
      rw [sub_sub_cancel] at this
      linarith
    have ra := radial_holder g hc K α hα0 hK hd a
    have rb := radial_holder g hc K α hα0 hK hd b
    have h2a : ‖a‖ ^ α ≤ (2 * ρ) ^ α := Real.rpow_le_rpow (norm_nonneg _) hna hα0.le
    have h2b : ‖b‖ ^ α ≤ (2 * ρ) ^ α := Real.rpow_le_rpow (norm_nonneg _) hnb hα0.le
    have h22 : (2 * ρ) ^ α ≤ 2 * ρ ^ α := by
      rw [Real.mul_rpow (by norm_num) hpos.le]
      gcongr
      calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
        _ = 2 := Real.rpow_one 2
    have htri : ‖g a - g b‖ ≤ ‖g a - g 0‖ + ‖g b - g 0‖ := by
      rw [show g a - g b = (g a - g 0) - (g b - g 0) by abel]; exact norm_sub_le _ _
    have hdiv : ∀ x : ℝ, 0 ≤ x → x / α ≤ x * (1 / α) := fun x _ => by rw [mul_one_div]
    have hK1 : K * (‖a‖ + ‖a‖ ^ α / α) ≤ K * (2 * ρ ^ α + 2 * ρ ^ α * (1 / α)) := by
      gcongr
      · linarith
      · rw [div_eq_mul_one_div]; gcongr; linarith
    have hK2 : K * (‖b‖ + ‖b‖ ^ α / α) ≤ K * (2 * ρ ^ α + 2 * ρ ^ α * (1 / α)) := by
      gcongr
      · linarith
      · rw [div_eq_mul_one_div]; gcongr; linarith
    nlinarith [mul_le_mul_of_nonneg_left hρa.le (by positivity : 0 ≤ 2 * B),
      mul_le_mul_of_nonneg_left hρa.le (by positivity : 0 ≤ 2 * K)]



lemma log_le_rpow (α r : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hr2 : r ≤ 2) :
    1 + |Real.log r| ≤ (2 + 1 / (1 - α)) * (1 + r ^ (α - 1)) := by
  have hp : 0 ≤ r ^ (α - 1) := Real.rpow_nonneg hr.le _
  have h1a : 0 < 1 - α := by linarith
  rcases le_or_gt r 1 with h1 | h1
  · have hl := Real.abs_log_mul_self_rpow_lt r (1 - α) hr h1 h1a
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr _)] at hl
    have hinv : r ^ (1 - α) * r ^ (α - 1) = 1 := by
      rw [← Real.rpow_add hr]; simp
    have : |Real.log r| ≤ r ^ (α - 1) / (1 - α) := by
      rw [le_div_iff₀ h1a]
      have := mul_lt_mul_of_pos_right hl (Real.rpow_pos_of_pos hr (α - 1))
      rw [mul_assoc, hinv, mul_one] at this
      have h' : 1 / (1 - α) * r ^ (α - 1) * (1 - α) = r ^ (α - 1) := by field_simp
      nlinarith [mul_lt_mul_of_pos_right this h1a]
    have h2 : r ^ (α - 1) / (1 - α) ≤ 1 / (1 - α) * (1 + r ^ (α - 1)) := by
      rw [div_eq_mul_one_div, mul_comm]; gcongr; linarith
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 + 1 / (1 - α)) hp]
  · have : |Real.log r| ≤ 1 := by
      rw [abs_of_nonneg (Real.log_nonneg h1.le)]
      have := Real.log_le_sub_one_of_pos hr
      linarith
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 + 1 / (1 - α)) hp,
      (by positivity : (0:ℝ) ≤ 1 / (1 - α))]

lemma fderiv_PsiK_eq (k : ℝ) (hk : 0 ≤ k) (y e : R2) (hy : y ≠ 0) :
    (fun w => fderiv ℝ (PsiK k) w e) =ᶠ[𝓝 y]
      fun w => dipoleSource k 0 e w - dipoleSource 0 0 e w := by
  filter_upwards [isOpen_ne.mem_nhds hy] with w hw
  have hev : PsiK k =ᶠ[𝓝 w] fun x => Phi k x 0 - Phi 0 x 0 := by
    filter_upwards [isOpen_ne.mem_nhds hw] with x hx
    rw [PsiK_eq k hk x 0 hx, sub_zero]
  have hdk : DifferentiableAt ℝ (fun x' => Phi k x' 0) w :=
    ((phi_contDiffOn2 k hk 0).differentiableOn (by norm_num) w hw).differentiableAt
      (isOpen_ne.mem_nhds hw)
  have hd0 : DifferentiableAt ℝ (fun x' => Phi 0 x' 0) w :=
    ((phi_contDiffOn2 0 le_rfl 0).differentiableOn (by norm_num) w hw).differentiableAt
      (isOpen_ne.mem_nhds hw)
  rw [hev.fderiv_eq, fderiv_fun_sub hdk hd0]
  rfl

lemma dipole_far_bound (k : ℝ) (hk : 0 < k) : ∃ C ≥ (0 : ℝ), ∀ e w : R2, 1 < ‖w‖ →
    ∃ D : R2 →L[ℝ] ℂ, HasFDerivAt (dipoleSource k 0 e) D w ∧ ‖D‖ ≤ C * ‖e‖ := by
  set A := k ^ 2 / 4
  have hA : 0 < A := by positivity
  obtain ⟨M1R, M2R, M3R, hM1R, hM2R, hM3R, hR1, hR2, B1R, B2R, B3R⟩ :=
    profile_higher (Rt A) (R1t A) A hA (((2 : ℝ) / 2) ^ 2) (by norm_num)
      (fun t ht => hasDerivAt_Rt A t ht.ne') (fun t ht => R1t_diff A t ht) (fun t ht => ode_Rt A t ht)
  obtain ⟨M1J, M2J, M3J, hM1J, hM2J, hM3J, hJ1, hJ2, B1J, B2J, B3J⟩ :=
    profile_higher (Jt A) (J1t A) A hA (((2 : ℝ) / 2) ^ 2) (by norm_num)
      (fun t _ => hasDerivAt_Jt A t) (fun t _ => J1t_diff A t) (fun t _ => ode_Jt A t)
  refine ⟨(4 * M2R + 2 * M1R / (2 / 2)) + ‖βk k‖ * (4 * M2J + 2 * M1J / (2 / 2)), by positivity,
    fun e w hw => ?_⟩
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  obtain ⟨D, hD, hDe⟩ := dipole_hasFDerivAt k hk 0 e w hw0
  refine ⟨D, hD, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_⟩
  have hw' : (2 : ℝ) / 2 < ‖w - 0‖ := by rw [sub_zero]; norm_num; exact hw
  have bR := (radial_dipole_bounds _ _ _ 0 e h 2 (by norm_num) M1R M2R M3R hM1R hM2R hM3R
    hR1 hR2 B1R B2R B3R w hw').2.1
  have bJ := (radial_dipole_bounds _ _ _ 0 e h 2 (by norm_num) M1J M2J M3J hM1J hM2J hM3J
    hJ1 hJ2 B1J B2J B3J w hw').2.1
  rw [hDe h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left bJ (norm_nonneg (βk k))
  nlinarith [norm_nonneg e, norm_nonneg h]

/-- hypotheses of `sing_holder` for the directional derivatives of `Ψ = PsiK k₁ - PsiK k₂` -/
lemma psi_grad_hyp (k1 k2 : ℝ) (hk1 : 0 < k1) (hk2 : 0 < k2) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (e : R2) :
    Continuous (fun w => fderiv ℝ (PsiK k1) w e - fderiv ℝ (PsiK k2) w e) ∧
    (∃ B, ∀ w, ‖fderiv ℝ (PsiK k1) w e - fderiv ℝ (PsiK k2) w e‖ ≤ B) ∧
    ∃ K ≥ (0 : ℝ), ∀ w : R2, w ≠ 0 → ∃ L : R2 →L[ℝ] ℂ,
      HasFDerivAt (fun w => fderiv ℝ (PsiK k1) w e - fderiv ℝ (PsiK k2) w e) L w ∧
        ‖L‖ ≤ K * (1 + ‖w‖ ^ (α - 1)) := by
  have hc : ∀ k, Continuous fun w => fderiv ℝ (PsiK k) w e := fun k =>
    ((PsiK_contDiff k).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hev : ∀ y : R2, y ≠ 0 → (fun w => fderiv ℝ (PsiK k1) w e - fderiv ℝ (PsiK k2) w e) =ᶠ[𝓝 y]
      fun w => dipoleSource k1 0 e w - dipoleSource k2 0 e w := by
    intro y hy
    filter_upwards [fderiv_PsiK_eq k1 hk1.le y e hy, fderiv_PsiK_eq k2 hk2.le y e hy] with w h1 h2
    rw [h1, h2]; ring
  refine ⟨(hc k1).sub (hc k2), ?_, ?_⟩
  · obtain ⟨B0, -, hB0⟩ := bound_closedBall 2 _ ((hc k1).sub (hc k2))
    obtain ⟨C1, hC1⟩ := pba k1 hk1 0 2 (by norm_num)
    obtain ⟨C2, hC2⟩ := pba k2 hk2 0 2 (by norm_num)
    refine ⟨max B0 ((C1 + C2) * ‖e‖), fun w => ?_⟩
    by_cases hw : ‖w‖ ≤ 2
    · exact (hB0 w (by rw [mem_closedBall, dist_zero_right]; exact hw)).trans (le_max_left _ _)
    · push Not at hw
      have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
      rw [(hev w hw0).eq_of_nhds]
      refine le_trans ?_ (le_max_right _ _)
      have h1 := (hC1 w (by rw [sub_zero]; exact hw.le)).2
      have h2 := (hC2 w (by rw [sub_zero]; exact hw.le)).2
      unfold dipoleSource
      refine (norm_sub_le _ _).trans ?_
      have a1 := (fderiv ℝ (fun x' => Phi k1 x' 0) w).le_opNorm e
      have a2 := (fderiv ℝ (fun x' => Phi k2 x' 0) w).le_opNorm e
      nlinarith [norm_nonneg e]
  · obtain ⟨K1, hK1, hK1b⟩ := PsiK_second k1 2
    obtain ⟨K2, hK2, hK2b⟩ := PsiK_second k2 2
    obtain ⟨D1, hD1, hD1b⟩ := dipole_far_bound k1 hk1
    obtain ⟨D2, hD2, hD2b⟩ := dipole_far_bound k2 hk2
    set Kn := (K1 + K2) * ‖e‖ * (2 + 1 / (1 - α))
    have h1a : 0 < 1 - α := by linarith
    refine ⟨max Kn ((D1 + D2) * ‖e‖), (by positivity : (0:ℝ) ≤ (D1 + D2) * ‖e‖).trans (le_max_right _ _), fun w hw => ?_⟩
    have hp : 0 ≤ ‖w‖ ^ (α - 1) := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hw2 : ‖w‖ ≤ 2
    · obtain ⟨G1, hG1, hG1b⟩ := hK1b e w hw hw2
      obtain ⟨G2, hG2, hG2b⟩ := hK2b e w hw hw2
      refine ⟨G1 - G2, hG1.sub hG2, ?_⟩
      have hlog := log_le_rpow α ‖w‖ hα0 hα1 (norm_pos_iff.mpr hw) hw2
      calc ‖G1 - G2‖ ≤ ‖G1‖ + ‖G2‖ := norm_sub_le _ _
        _ ≤ K1 * (1 + |Real.log ‖w‖|) * ‖e‖ + K2 * (1 + |Real.log ‖w‖|) * ‖e‖ :=
            add_le_add hG1b hG2b
        _ = (K1 + K2) * ‖e‖ * (1 + |Real.log ‖w‖|) := by ring
        _ ≤ (K1 + K2) * ‖e‖ * ((2 + 1 / (1 - α)) * (1 + ‖w‖ ^ (α - 1))) := by gcongr
        _ = Kn * (1 + ‖w‖ ^ (α - 1)) := by ring
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · push Not at hw2
      obtain ⟨E1', hE1, hE1b⟩ := hD1b e w (by linarith)
      obtain ⟨E2', hE2, hE2b⟩ := hD2b e w (by linarith)
      refine ⟨E1' - E2', (hE1.sub hE2).congr_of_eventuallyEq (hev w hw), ?_⟩
      calc ‖E1' - E2'‖ ≤ ‖E1'‖ + ‖E2'‖ := norm_sub_le _ _
        _ ≤ (D1 + D2) * ‖e‖ := by nlinarith
        _ ≤ max Kn ((D1 + D2) * ‖e‖) := le_max_right _ _
        _ ≤ max Kn ((D1 + D2) * ‖e‖) * (1 + ‖w‖ ^ (α - 1)) := by
            have h0 : (0:ℝ) ≤ max Kn ((D1 + D2) * ‖e‖) :=
              (by positivity : (0:ℝ) ≤ (D1 + D2) * ‖e‖).trans (le_max_right _ _)
            nlinarith



/-- quantitative bounded Hölder class on `Γ` -/
def HQ {E : Type*} [NormedAddCommGroup E] (f : ℝ → ℝ) (α : ℝ) (φ : ℝ → E) (B H : ℝ) : Prop :=
  Continuous φ ∧ (∀ s, ‖φ s‖ ≤ B) ∧ ∀ s t, ‖φ s - φ t‖ ≤ H * ‖gpt f s - gpt f t‖ ^ α

section
variable {E : Type*} [NormedAddCommGroup E] (f : ℝ → ℝ) (α : ℝ)

lemma HQ.isBC0 {φ : ℝ → E} {B H : ℝ} (h : HQ f α φ B H) : IsBC0AlphaGam f α φ :=
  ⟨h.1, ⟨B, h.2.1⟩, H, h.2.2⟩

lemma HQ.B_nonneg {φ : ℝ → E} {B H : ℝ} (h : HQ f α φ B H) : 0 ≤ B :=
  (norm_nonneg _).trans (h.2.1 0)

lemma HQ.holderNorm0_le {φ : ℝ → E} {B H : ℝ} (h : HQ f α φ B H) (hH : 0 ≤ H) :
    holderNorm0 f α φ ≤ B + H := by
  have hB := h.B_nonneg
  unfold holderNorm0 supNormGam
  refine add_le_add (Real.iSup_le (fun s => h.2.1 s) hB) (Real.iSup_le (fun p => ?_) hH)
  have hpos : 0 < ‖gpt f p.1.1 - gpt f p.1.2‖ := by
    have := abs_sub_le_gpt f p.1.1 p.1.2
    have : 0 < |p.1.1 - p.1.2| := abs_pos.mpr (sub_ne_zero.mpr p.2)
    linarith
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos α)]
  exact h.2.2 _ _

lemma HQ.add {φ ψ : ℝ → E} {B1 H1 B2 H2 : ℝ} (h1 : HQ f α φ B1 H1) (h2 : HQ f α ψ B2 H2) :
    HQ f α (fun s => φ s + ψ s) (B1 + B2) (H1 + H2) := by
  refine ⟨h1.1.add h2.1, fun s => (norm_add_le _ _).trans (add_le_add (h1.2.1 s) (h2.2.1 s)),
    fun s t => ?_⟩
  rw [show φ s + ψ s - (φ t + ψ t) = (φ s - φ t) + (ψ s - ψ t) by abel]
  refine (norm_add_le _ _).trans ?_
  have := h1.2.2 s t; have := h2.2.2 s t
  linarith

lemma HQ.neg {φ : ℝ → E} {B H : ℝ} (h : HQ f α φ B H) : HQ f α (fun s => -φ s) B H :=
  ⟨h.1.neg, fun s => by rw [norm_neg]; exact h.2.1 s, fun s t => by
    rw [show -φ s - -φ t = -(φ s - φ t) by abel, norm_neg]; exact h.2.2 s t⟩

lemma HQ.mono {φ : ℝ → E} {B H B' H' : ℝ} (h : HQ f α φ B H) (hB : B ≤ B') (hH : H ≤ H') :
    HQ f α φ B' H' :=
  ⟨h.1, fun s => (h.2.1 s).trans hB, fun s t => (h.2.2 s t).trans
    (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg _) _))⟩
end

lemma HQ.mul (f : ℝ → ℝ) (α : ℝ) {φ ψ : ℝ → ℂ} {B1 H1 B2 H2 : ℝ} (h1 : HQ f α φ B1 H1)
    (h2 : HQ f α ψ B2 H2) : HQ f α (fun s => φ s * ψ s) (B1 * B2) (B1 * H2 + B2 * H1) := by
  have hB1 := h1.B_nonneg; have hB2 := h2.B_nonneg
  refine ⟨h1.1.mul h2.1, fun s => ?_, fun s t => ?_⟩
  · rw [norm_mul]; exact mul_le_mul (h1.2.1 s) (h2.2.1 s) (norm_nonneg _) hB1
  · rw [show φ s * ψ s - φ t * ψ t = φ s * (ψ s - ψ t) + ψ t * (φ s - φ t) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hr := Real.rpow_nonneg (norm_nonneg (gpt f s - gpt f t)) α
    calc ‖φ s‖ * ‖ψ s - ψ t‖ + ‖ψ t‖ * ‖φ s - φ t‖ ≤
        B1 * (H2 * ‖gpt f s - gpt f t‖ ^ α) + B2 * (H1 * ‖gpt f s - gpt f t‖ ^ α) := by
          gcongr
          · exact h1.2.1 s
          · exact h2.2.2 s t
          · exact h2.2.1 t
          · exact h1.2.2 s t
      _ = _ := by ring

lemma HQ.const (f : ℝ → ℝ) (α : ℝ) (c : ℂ) : HQ f α (fun _ => c) ‖c‖ 0 :=
  ⟨continuous_const, fun _ => le_rfl, fun s t => by simp⟩

/-- functions Lipschitz in `s` (hence in the distance on `Γ`) are Hölder -/
lemma HQ.of_lip (f : ℝ → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (φ : ℝ → ℂ) (hc : Continuous φ)
    (B L : ℝ) (hL : 0 ≤ L) (hB : ∀ s, ‖φ s‖ ≤ B) (hlip : ∀ s t, ‖φ s - φ t‖ ≤ L * ‖gpt f s - gpt f t‖) :
    HQ f α φ B (L + 2 * B) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨hc, hB, fun s t => ?_⟩
  set r := ‖gpt f s - gpt f t‖
  have hr0 : 0 ≤ r := norm_nonneg _
  rcases le_or_gt r 1 with h | h
  · have : r ≤ r ^ α := by
      rcases eq_or_lt_of_le hr0 with h0 | h0
      · rw [← h0, Real.zero_rpow hα0.ne']
      · calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
          _ ≤ r ^ α := Real.rpow_le_rpow_of_exponent_ge h0 h hα1
    have := hlip s t
    nlinarith [Real.rpow_nonneg hr0 α]
  · have h1 : 1 ≤ r ^ α := Real.one_le_rpow h.le hα0.le
    have := (norm_sub_le (φ s) (φ t)).trans (add_le_add (hB s) (hB t))
    nlinarith [Real.rpow_nonneg hr0 α]

lemma HQ.vec2 (f : ℝ → ℝ) (α : ℝ) {a b : ℝ → ℂ} {B1 H1 B2 H2 : ℝ} (ha : HQ f α a B1 H1)
    (hb : HQ f α b B2 H2) :
    HQ f α (fun s => (!₂[a s, b s] : EuclideanSpace ℂ (Fin 2))) (B1 + B2) (H1 + H2) := by
  have hnorm : ∀ x y : ℂ, ‖(!₂[x, y] : EuclideanSpace ℂ (Fin 2))‖ ≤ ‖x‖ + ‖y‖ := by
    intro x y
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, PiLp.toLp_apply]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg x, norm_nonneg y]
  refine ⟨?_, fun s => (hnorm _ _).trans (add_le_add (ha.2.1 s) (hb.2.1 s)), fun s t => ?_⟩
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using ha.1
    · simpa using hb.1
  · have e : (!₂[a s, b s] : EuclideanSpace ℂ (Fin 2)) - !₂[a t, b t] = !₂[a s - a t, b s - b t] := by
      ext i; fin_cases i <;> simp
    rw [e]
    refine (hnorm _ _).trans ?_
    have := ha.2.2 s t; have := hb.2.2 s t
    linarith



lemma phi_translate (k : ℝ) (x z : R2) : Phi k x z = Phi k (x - z) 0 := by
  simp [Phi]

lemma phi_fun_translate (k : ℝ) (z : R2) :
    (fun x => Phi k x z) = fun x => Phi k (x - z) 0 := funext fun x => phi_translate k x z

lemma dipole_translate (k : ℝ) (z e : R2) :
    dipoleSource k z e = fun x => dipoleSource k 0 e (x - z) := by
  funext x
  unfold dipoleSource
  rw [phi_fun_translate k z, fderiv_comp_sub (f := fun w => Phi k w 0) z]

lemma dipole_far_bound' (k : ℝ) (hk : 0 < k) (d : ℝ) (hd : 0 < d) :
    ∃ C ≥ (0 : ℝ), ∀ e w : R2, d / 2 < ‖w‖ →
    ∃ D : R2 →L[ℝ] ℂ, HasFDerivAt (dipoleSource k 0 e) D w ∧ ‖D‖ ≤ C * ‖e‖ := by
  set A := k ^ 2 / 4
  have hA : 0 < A := by positivity
  obtain ⟨M1R, M2R, M3R, hM1R, hM2R, hM3R, hR1, hR2, B1R, B2R, B3R⟩ :=
    profile_higher (Rt A) (R1t A) A hA ((d / 2) ^ 2) (by positivity)
      (fun t ht => hasDerivAt_Rt A t ht.ne') (fun t ht => R1t_diff A t ht) (fun t ht => ode_Rt A t ht)
  obtain ⟨M1J, M2J, M3J, hM1J, hM2J, hM3J, hJ1, hJ2, B1J, B2J, B3J⟩ :=
    profile_higher (Jt A) (J1t A) A hA ((d / 2) ^ 2) (by positivity)
      (fun t _ => hasDerivAt_Jt A t) (fun t _ => J1t_diff A t) (fun t _ => ode_Jt A t)
  refine ⟨(4 * M2R + 2 * M1R / (d / 2)) + ‖βk k‖ * (4 * M2J + 2 * M1J / (d / 2)), by positivity,
    fun e w hw => ?_⟩
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  obtain ⟨D, hD, hDe⟩ := dipole_hasFDerivAt k hk 0 e w hw0
  refine ⟨D, hD, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_⟩
  have hw' : d / 2 < ‖w - 0‖ := by rw [sub_zero]; exact hw
  have bR := (radial_dipole_bounds _ _ _ 0 e h d hd M1R M2R M3R hM1R hM2R hM3R
    hR1 hR2 B1R B2R B3R w hw').2.1
  have bJ := (radial_dipole_bounds _ _ _ 0 e h d hd M1J M2J M3J hM1J hM2J hM3J
    hJ1 hJ2 B1J B2J B3J w hw').2.1
  rw [hDe h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left bJ (norm_nonneg (βk k))
  nlinarith [norm_nonneg e, norm_nonneg h]

/-- uniform bounds for `Φ_k(·, z)` and its first two derivatives at distance `> d/2`,
independent of `z` -/
lemma phi_uniform_bounds (k : ℝ) (hk : 0 < k) (d : ℝ) (hd : 0 < d) :
    ∃ C ≥ (0 : ℝ), ∀ z x : R2, d / 2 < ‖x - z‖ →
      ‖Phi k x z‖ ≤ C ∧ ‖fderiv ℝ (fun x' => Phi k x' z) x‖ ≤ C ∧
      ∀ e, ∃ D : R2 →L[ℝ] ℂ, HasFDerivAt (dipoleSource k z e) D x ∧ ‖D‖ ≤ C * ‖e‖ := by
  obtain ⟨C0, hC0⟩ := pba k hk 0 (d / 2) (by positivity)
  obtain ⟨C2, hC2, hC2b⟩ := dipole_far_bound' k hk d hd
  refine ⟨max (max C0 0) C2, le_max_of_le_left (le_max_right _ _), fun z x hx => ⟨?_, ?_, fun e => ?_⟩⟩
  · rw [phi_translate]
    exact ((hC0 (x - z) (by rw [sub_zero]; exact hx.le)).1).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · rw [phi_fun_translate, fderiv_comp_sub (f := fun w => Phi k w 0) z]
    exact ((hC0 (x - z) (by rw [sub_zero]; exact hx.le)).2).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · obtain ⟨D, hD, hDb⟩ := hC2b e (x - z) hx
    refine ⟨D, ?_, hDb.trans (by gcongr; exact le_max_right _ _)⟩
    rw [dipole_translate]
    have h := hD.comp x ((hasFDerivAt_id x).sub_const z)
    rw [ContinuousLinearMap.comp_id] at h
    exact h



lemma far_part_bounds (k : ℝ) (hk : 0 < k) (χ : R2 → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hcs : HasCompactSupport χ) (x0 : R2) (hχ1 : ∀ x ∈ ball x0 1, χ x = 1) :
    ∃ B K K2 : ℝ, 0 ≤ K ∧ 0 ≤ K2 ∧ ∀ z ∈ ball x0 (1 / 2),
      (∀ x, ‖((1 - χ x : ℝ) : ℂ) * Phi k x z‖ ≤ B) ∧
      (∀ x, ∃ D : R2 →L[ℝ] ℂ, HasFDerivAt (fun y => ((1 - χ y : ℝ) : ℂ) * Phi k y z) D x ∧ ‖D‖ ≤ K) ∧
      ∀ e x, ∃ L : R2 →L[ℝ] ℂ,
        HasFDerivAt (fun y => fderiv ℝ (fun y => ((1 - χ y : ℝ) : ℂ) * Phi k y z) y e) L x ∧
          ‖L‖ ≤ K2 * ‖e‖ := by
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hχd : Differentiable ℝ χ := hχ2.differentiable (by norm_num)
  have hχ1c : ContDiff ℝ 1 (fderiv ℝ χ) := hχ2.fderiv_right (by norm_num)
  have hχ1d : Differentiable ℝ (fderiv ℝ χ) := hχ1c.differentiable one_ne_zero
  obtain ⟨M0, hM0⟩ := hχ2.continuous.bounded_above_of_compact_support hcs
  obtain ⟨M1, hM1⟩ := (hχ2.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hcs.fderiv (𝕜 := ℝ))
  obtain ⟨M2, hM2⟩ := (hχ1c.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    ((hcs.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  obtain ⟨C, hC0, hC⟩ := phi_uniform_bounds k hk 1 one_pos
  have hM1n : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hM2n : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0)
  have hM0n : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  set K := (1 + M0) * C + C * M1
  set K2 := (1 + M0) * C + 2 * C * M1 + C * M2
  refine ⟨(1 + M0) * C, K, K2, by positivity, by positivity, fun z hz => ?_⟩
  set F : R2 → ℂ := fun y => ((1 - χ y : ℝ) : ℂ) * Phi k y z with hF
  have hzx0 : ‖z - x0‖ < 1 / 2 := by rw [mem_ball, dist_eq_norm] at hz; exact hz
  -- the two regions
  have hreg : ∀ x, x ∈ ball x0 1 ∨ 1 / 2 < ‖x - z‖ := by
    intro x
    by_cases hx : x ∈ ball x0 1
    · exact Or.inl hx
    · right
      rw [mem_ball, dist_eq_norm, not_lt] at hx
      have := norm_sub_le_norm_sub_add_norm_sub x z x0
      linarith
  have hzero : ∀ x ∈ ball x0 1, F =ᶠ[𝓝 x] fun _ => 0 := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    simp [hF, hχ1 y hy]
  have hU2 : ∀ x, 1 / 2 < ‖x - z‖ → x ≠ z := fun x hx h => by
    rw [h, sub_self, norm_zero] at hx; linarith
  have hdiffΦ : ∀ y : R2, y ≠ z → DifferentiableAt ℝ (fun x' => Phi k x' z) y := fun y hy =>
    ((phi_contDiffOn2 k hk.le z).differentiableOn (by norm_num) y hy).differentiableAt
      (isOpen_ne.mem_nhds hy)
  have ha : ∀ y, HasFDerivAt (fun y => ((1 - χ y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (-fderiv ℝ χ y)) y := fun y =>
    Complex.ofRealCLM.hasFDerivAt.comp y ((hχd y).hasFDerivAt.const_sub 1)
  have hFd : ∀ y, y ≠ z → HasFDerivAt F (((1 - χ y : ℝ) : ℂ) • fderiv ℝ (fun x' => Phi k x' z) y +
      Phi k y z • Complex.ofRealCLM.comp (-fderiv ℝ χ y)) y := fun y hy =>
    (ha y).mul (hdiffΦ y hy).hasFDerivAt
  have hχb : ∀ y, |1 - χ y| ≤ 1 + M0 := fun y => by
    have := hM0 y; rw [Real.norm_eq_abs] at this
    calc |1 - χ y| ≤ |1| + |χ y| := abs_sub _ _
      _ ≤ 1 + M0 := by rw [abs_one]; linarith
  have hsm : ∀ (c : ℂ) (L : R2 →L[ℝ] ℂ), ‖c • L‖ ≤ ‖c‖ * ‖L‖ := fun c L => norm_smul_le c L
  refine ⟨fun x => ?_, fun x => ?_, fun e x => ?_⟩
  · rcases hreg x with hx | hx
    · show ‖F x‖ ≤ _
      rw [(hzero x hx).eq_of_nhds, norm_zero]; positivity
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hχb x) (hC z x (by norm_num; exact hx)).1 (norm_nonneg _) (by positivity)
  · rcases hreg x with hx | hx
    · exact ⟨0, (hasFDerivAt_const 0 x).congr_of_eventuallyEq (hzero x hx), by
        rw [norm_zero]; positivity⟩
    · refine ⟨_, hFd x (hU2 x hx), ?_⟩
      have hb := hC z x (by norm_num; exact hx)
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((hsm _ _).trans ?_) ((hsm _ _).trans ?_)
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hχb x) hb.2.1 (norm_nonneg _) (by positivity)
      · have h1 : ‖Complex.ofRealCLM.comp (-fderiv ℝ χ x)‖ ≤ M1 := by
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          rw [Complex.ofRealCLM_norm, one_mul, norm_neg]; exact hM1 x
        exact mul_le_mul hb.1 h1 (norm_nonneg _) hC0
  · rcases hreg x with hx | hx
    · refine ⟨0, (hasFDerivAt_const 0 x).congr_of_eventuallyEq ?_, by rw [norm_zero]; positivity⟩
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      rw [(hzero y hy).fderiv_eq, fderiv_const_apply, ContinuousLinearMap.zero_apply]
    · have hev : (fun y => fderiv ℝ F y e) =ᶠ[𝓝 x] fun y =>
          ((1 - χ y : ℝ) : ℂ) * dipoleSource k z e y + Phi k y z * ((-(fderiv ℝ χ y e) : ℝ) : ℂ) := by
        have hopen : IsOpen {y : R2 | 1 / 2 < ‖y - z‖} :=
          isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
        filter_upwards [hopen.mem_nhds hx] with y hy
        rw [(hFd y (hU2 y hy)).fderiv]
        simp [dipoleSource, smul_eq_mul]
      have hb := hC z x (by norm_num; exact hx)
      obtain ⟨Dd, hDd, hDdb⟩ := hb.2.2 e
      have hce : HasFDerivAt (fun y => ((-(fderiv ℝ χ y e) : ℝ) : ℂ))
          (Complex.ofRealCLM.comp (-((ContinuousLinearMap.apply ℝ ℝ e).comp
            (fderiv ℝ (fderiv ℝ χ) x)))) x :=
        Complex.ofRealCLM.hasFDerivAt.comp x
          (((ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp x (hχ1d x).hasFDerivAt).neg)
      have hT := ((ha x).mul hDd).add ((hdiffΦ x (hU2 x hx)).hasFDerivAt.mul hce)
      refine ⟨_, hT.congr_of_eventuallyEq hev, ?_⟩
      have hdipx : ‖dipoleSource k z e x‖ ≤ C * ‖e‖ := by
        unfold dipoleSource
        exact ((fderiv ℝ (fun x' => Phi k x' z) x).le_opNorm e).trans (by gcongr; exact hb.2.1)
      have hχe : ‖((-(fderiv ℝ χ x e) : ℝ) : ℂ)‖ ≤ M1 * ‖e‖ := by
        rw [Complex.norm_real, norm_neg]
        exact ((fderiv ℝ χ x).le_opNorm e).trans (by gcongr; exact hM1 x)
      have hn1 : ‖Complex.ofRealCLM.comp (-fderiv ℝ χ x)‖ ≤ M1 := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [Complex.ofRealCLM_norm, one_mul, norm_neg]; exact hM1 x
      have hn2 : ‖Complex.ofRealCLM.comp (-((ContinuousLinearMap.apply ℝ ℝ e).comp
          (fderiv ℝ (fderiv ℝ χ) x)))‖ ≤ M2 * ‖e‖ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [Complex.ofRealCLM_norm, one_mul, norm_neg]
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
        calc ‖fderiv ℝ (fderiv ℝ χ) x h e‖ ≤ ‖fderiv ℝ (fderiv ℝ χ) x h‖ * ‖e‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ (‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖h‖) * ‖e‖ := by
              gcongr; exact ContinuousLinearMap.le_opNorm _ _
          _ ≤ (M2 * ‖h‖) * ‖e‖ := by gcongr; exact hM2 x
          _ = M2 * ‖e‖ * ‖h‖ := by ring
      have hsm : ∀ (c : ℂ) (L : R2 →L[ℝ] ℂ), ‖c • L‖ ≤ ‖c‖ * ‖L‖ := fun c L => norm_smul_le c L
      calc _ ≤ (‖((1 - χ x : ℝ) : ℂ) • Dd‖ + ‖dipoleSource k z e x • Complex.ofRealCLM.comp
              (-fderiv ℝ χ x)‖) + (‖Phi k x z • Complex.ofRealCLM.comp
              (-((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ χ) x)))‖ +
              ‖((-(fderiv ℝ χ x e) : ℝ) : ℂ) • fderiv ℝ (fun x' => Phi k x' z) x‖) :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
        _ ≤ ((1 + M0) * (C * ‖e‖) + (C * ‖e‖) * M1) + (C * (M2 * ‖e‖) + (M1 * ‖e‖) * C) := by
            gcongr
            · refine (hsm _ _).trans ?_
              rw [Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul (hχb x) hDdb (norm_nonneg _) (by positivity)
            · exact (hsm _ _).trans (mul_le_mul hdipx hn1 (norm_nonneg _) (by positivity))
            · exact (hsm _ _).trans (mul_le_mul hb.1 hn2 (norm_nonneg _) hC0)
            · exact (hsm _ _).trans (mul_le_mul hχe hb.2.1 (norm_nonneg _) (by positivity))
        _ = K2 * ‖e‖ := by simp only [K2]; ring



lemma abs_coord_le_norm' (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

lemma vec_eq_basis (h : R2) : h = h 0 • E0 + h 1 • E1 := by
  ext i; fin_cases i <;> simp

lemma clm_norm_basis (L : R2 →L[ℝ] ℂ) : ‖L‖ ≤ ‖L E0‖ + ‖L E1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  conv_lhs => rw [vec_eq_basis h]
  rw [map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have := abs_coord_le_norm' h 0; have := abs_coord_le_norm' h 1
  nlinarith [norm_nonneg (L E0), norm_nonneg (L E1)]

lemma lip_of_deriv (u : R2 → ℂ) (K : ℝ)
    (hu : ∀ x, ∃ L : R2 →L[ℝ] ℂ, HasFDerivAt u L x ∧ ‖L‖ ≤ K) :
    ∀ a b, ‖u a - u b‖ ≤ K * ‖a - b‖ := by
  intro a b
  choose L hL hLb using hu
  have := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := u) (f' := L)
    (fun x _ => (hL x).hasFDerivWithinAt) (fun x _ => hLb x) (Set.mem_univ b) (Set.mem_univ a)
  exact this

lemma HQ.of_global_lip (f : ℝ → ℝ) (hfc : Continuous f) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (u : R2 → ℂ) (B K : ℝ) (hK : 0 ≤ K) (hB : ∀ x, ‖u x‖ ≤ B)
    (hu : ∀ x, ∃ L : R2 →L[ℝ] ℂ, HasFDerivAt u L x ∧ ‖L‖ ≤ K) (z : R2) :
    HQ f α (fun s => u (gpt f s - z)) B (K + 2 * B) := by
  have hgc : Continuous (gpt f) := by unfold gpt pt; fun_prop
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun x =>
    (hu x).choose_spec.1.continuousAt
  refine HQ.of_lip f α hα0 hα1 _ (huc.comp (hgc.sub continuous_const)) B K hK
    (fun s => hB _) fun s t => ?_
  have := lip_of_deriv u K hu (gpt f s - z) (gpt f t - z)
  rwa [sub_sub_sub_cancel_right] at this

lemma HQ.of_sing (f : ℝ → ℝ) (hfc : Continuous f) (α : ℝ) (g : R2 → ℂ) (hc : Continuous g) (B H : ℝ)
    (hB : ∀ x, ‖g x‖ ≤ B) (hH : ∀ a b, ‖g a - g b‖ ≤ H * ‖a - b‖ ^ α) (z : R2) :
    HQ f α (fun s => g (gpt f s - z)) B H := by
  have hgc : Continuous (gpt f) := by unfold gpt pt; fun_prop
  refine ⟨hc.comp (hgc.sub continuous_const), fun s => hB _, fun s t => ?_⟩
  have := hH (gpt f s - z) (gpt f t - z)
  rwa [sub_sub_sub_cancel_right] at this

/-- Hölder pieces built from `f'` -/
lemma deriv_pieces (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ B1 H1 B2 H2 B3 H3 : ℝ,
      HQ f α (fun s => ((deriv f s : ℝ) : ℂ)) B1 H1 ∧
      HQ f α (fun s => (((1 + deriv f s ^ 2)⁻¹ : ℝ) : ℂ)) B2 H2 ∧
      HQ f α (fun s => (((arcDen f s)⁻¹ : ℝ) : ℂ)) B3 H3 := by
  obtain ⟨Cd, hCd⟩ := hf.2.2.2.1
  obtain ⟨Cl, hCl⟩ := hf.2.2.2.2
  have hlip : ∀ s t, |deriv f s - deriv f t| ≤ max Cl 0 * ‖gpt f s - gpt f t‖ := by
    intro s t
    have := hCl s t
    rw [Real.rpow_one] at this
    calc _ ≤ Cl * |s - t| := this
      _ ≤ max Cl 0 * |s - t| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      _ ≤ max Cl 0 * ‖gpt f s - gpt f t‖ :=
          mul_le_mul_of_nonneg_left (abs_sub_le_gpt f s t) (le_max_right _ _)
  refine ⟨_, _, _, _, _, _, HQ.of_lip f α hα0 hα1 (fun s => ((deriv f s : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hf.2.1 : Continuous fun s => ((deriv f s : ℝ) : ℂ)) Cd
    (max Cl 0) (le_max_right _ _) (fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hCd s)
    (fun s t => by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hlip s t),
    HQ.of_lip f α hα0 hα1 _ ?_ 1 (2 * max Cl 0) (mul_nonneg zero_le_two (le_max_right _ _))
      (fun s => ?_) (fun s t => ?_),
    HQ.of_lip f α hα0 hα1 _ ?_ 1 (max Cl 0) (le_max_right _ _) (fun s => ?_) (fun s t => ?_)⟩
  · exact Complex.continuous_ofReal.comp ((continuous_const.add (hf.2.1.pow 2)).inv₀
      fun s => (by positivity : (0:ℝ) < 1 + deriv f s ^ 2).ne')
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (deriv f s)])
  · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (inv_sq_lip _ _).trans ?_
    have := hlip s t
    linarith
  · refine Complex.continuous_ofReal.comp (Continuous.inv₀ ?_ fun s => ?_)
    · unfold arcDen; exact (continuous_const.add (hf.2.1.pow 2)).sqrt
    · exact (Real.sqrt_pos.mpr (by positivity)).ne'
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
      (show 0 < arcDen f s from Real.sqrt_pos.mpr (by positivity)))]
    exact inv_le_one_of_one_le₀ (by rw [arcDen, Real.one_le_sqrt]; nlinarith [sq_nonneg (deriv f s)])
  · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (inv_sqrt_lip _ _).trans (hlip s t)



lemma abs_coord_le_norm (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

lemma normal_norm (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < arcDen f s := Real.sqrt_pos.mpr (by positivity)
  have hpt : ‖pt (deriv f s) (-1)‖ = arcDen f s := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [pt, arcDen]
    ring_nf
  rw [normal, norm_smul, hpt, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- Mirror of `cone_below_interface`: points in a cone around `-n` lie above `Γ`. -/
lemma cone_above_interface (f : ℝ → ℝ) (s0 : ℝ) (hf : DifferentiableAt ℝ f s0) :
    ∃ r > (0 : ℝ), ∀ v : R2, v ≠ 0 → ‖v‖ < r →
      ‖v‖ ≤ -(2 * @inner ℝ R2 _ v (normal f s0)) → gpt f s0 + v ∈ Dplus f := by
  set d := deriv f s0 with hd
  set a := arcDen f s0 with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hlo := hf.hasDerivAt.isLittleO
  have hev := hlo.def (c := a / 4) (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, fun v hv0 hvr hcone => ?_⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hinner : @inner ℝ R2 _ v (normal f s0) = a⁻¹ * (d * v 0 - v 1) := by
    simp [normal, pt, ← ha, ← hd, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_right]
    ring_nf
    try simp
  rw [hinner] at hcone
  have hkey : a * ‖v‖ ≤ 2 * (v 1 - d * v 0) := by
    have := mul_le_mul_of_nonneg_left hcone hapos.le
    calc a * ‖v‖ ≤ a * -(2 * (a⁻¹ * (d * v 0 - v 1))) := this
      _ = 2 * (v 1 - d * v 0) := by field_simp; ring
  have h0 := abs_coord_le_norm v 0
  have hdist : dist (s0 + v 0) s0 < r := by
    rw [Real.dist_eq, add_sub_cancel_left]; linarith
  have htay := hball hdist
  simp only [add_sub_cancel_left, Real.norm_eq_abs, smul_eq_mul] at htay
  have hup : f (s0 + v 0) ≤ f s0 + v 0 * d + a / 4 * |v 0| := by
    have := (abs_le.mp htay).2
    linarith
  show f ((gpt f s0 + v) 0) < (gpt f s0 + v) 1
  simp only [gpt, pt, PiLp.add_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have : a / 4 * |v 0| ≤ a / 4 * ‖v‖ := mul_le_mul_of_nonneg_left h0 (by positivity)
  nlinarith




noncomputable def gPsi (k1 k2 : ℝ) (e w : R2) : ℂ := fderiv ℝ (PsiK k1) w e - fderiv ℝ (PsiK k2) w e

lemma gPsi_lin (k1 k2 : ℝ) (a b : ℝ) (w : R2) :
    gPsi k1 k2 (a • E0 + b • E1) w = (a : ℂ) * gPsi k1 k2 E0 w + (b : ℂ) * gPsi k1 k2 E1 w := by
  simp only [gPsi, map_add, map_smul, Complex.real_smul]; ring

/-- the singular part: `Φ_{k₁} - Φ_{k₂}` and its gradient along `Γ` -/
lemma psi_identities (k1 k2 : ℝ) (hk1 : 0 < k1) (hk2 : 0 < k2) (z x : R2) (hx : x ≠ z) :
    Phi k1 x z - Phi k2 x z = PsiK k1 (x - z) - PsiK k2 (x - z) ∧
    ∀ e, fderiv ℝ (fun x' => Phi k1 x' z) x e - fderiv ℝ (fun x' => Phi k2 x' z) x e =
      gPsi k1 k2 e (x - z) := by
  have hw : x - z ≠ 0 := sub_ne_zero.mpr hx
  refine ⟨?_, fun e => ?_⟩
  · rw [← PsiK_eq k1 hk1.le x z hx, ← PsiK_eq k2 hk2.le x z hx]; ring
  · have h1 := (fderiv_PsiK_eq k1 hk1.le (x - z) e hw).eq_of_nhds
    have h2 := (fderiv_PsiK_eq k2 hk2.le (x - z) e hw).eq_of_nhds

    unfold gPsi
    rw [h1, h2]
    have t1 := congrFun (dipole_translate k1 z e) x
    have t2 := congrFun (dipole_translate k2 z e) x
    unfold dipoleSource at t1 t2 ⊢
    rw [← t1, ← t2]
    ring



lemma HQ.congr {E : Type*} [NormedAddCommGroup E] {f : ℝ → ℝ} {α : ℝ} {φ ψ : ℝ → E} {B H : ℝ}
    (h : HQ f α φ B H) (e : ∀ s, φ s = ψ s) : HQ f α ψ B H := by
  have : φ = ψ := funext e
  rwa [← this]

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ χ : R2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        (∀ x ∈ Metric.ball (gpt f s0) 1, χ x = 1) →
      ∀ α : ℝ, 0 < α → α < 1 →
      ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
        IsBC1AlphaGam f α (fun s =>
          (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) *
            Phi kp (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0) -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0))) ∧
        IsBC0AlphaGam f α (fun s =>
          (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).2 s - 0 -
          -((μ : ℂ) * (((μ⁻¹ : ℝ) : ℂ) * fderiv ℝ
            (fun x => Phi km x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) (gpt f s) (normal f s)))) ∧
        holderNorm1 f α (fun s =>
          (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) *
            Phi kp (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0) -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0))) +
        holderNorm0 f α (fun s =>
          (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).2 s - 0 -
          -((μ : ℂ) * (((μ⁻¹ : ℝ) : ℂ) * fderiv ℝ
            (fun x => Phi km x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) (gpt f s) (normal f s))))
          ≤ C := by
  have hfc : Continuous f := hf.1.continuous
  have hkp : 0 < kp := hpar.1
  have hkm : 0 < km := hpar.2.1
  have hμ : 0 < μ := hpar.2.2.1
  obtain ⟨r, hr, hcone⟩ := cone_above_interface f s0 (hf.1 s0)
  refine ⟨min r (1 / 2), lt_min hr (by norm_num),
    fun δ hδ hδ0 χ hχ1 hχ2 hχ3 α hα0 hα1 => ?_⟩
  have hδr : δ < r := lt_of_lt_of_le hδ0 (min_le_left _ _)
  have hδh : δ < 1 / 2 := lt_of_lt_of_le hδ0 (min_le_right _ _)
  set x0 := gpt f s0 with hx0
  -- singular part: gradient pieces
  obtain ⟨hcE0, ⟨BE0, hBE0⟩, KE0, hKE0, hdE0⟩ := psi_grad_hyp km kp hkm hkp α hα0 hα1 E0
  obtain ⟨hcE1, ⟨BE1, hBE1⟩, KE1, hKE1, hdE1⟩ := psi_grad_hyp km kp hkm hkp α hα0 hα1 E1
  have hQ0 := fun z => HQ.of_sing f hfc α (gPsi km kp E0) hcE0 BE0 _ hBE0
    (sing_holder _ hcE0 BE0 KE0 α hα0 hα1 hKE0 hBE0 hdE0) z
  have hQ1 := fun z => HQ.of_sing f hfc α (gPsi km kp E1) hcE1 BE1 _ hBE1
    (sing_holder _ hcE1 BE1 KE1 α hα0 hα1 hKE1 hBE1 hdE1) z
  -- singular part: values
  set Ψ : R2 → ℂ := fun w => PsiK km w - PsiK kp w with hΨ
  have hΨd : ∀ w, HasFDerivAt Ψ (fderiv ℝ (PsiK km) w - fderiv ℝ (PsiK kp) w) w := fun w =>
    ((PsiK_contDiff km).differentiable one_ne_zero w).hasFDerivAt.sub
      ((PsiK_contDiff kp).differentiable one_ne_zero w).hasFDerivAt
  have hBE0n : 0 ≤ BE0 := (norm_nonneg _).trans (hBE0 0)
  have hBE1n : 0 ≤ BE1 := (norm_nonneg _).trans (hBE1 0)
  have hΨdb : ∀ w, ‖fderiv ℝ (PsiK km) w - fderiv ℝ (PsiK kp) w‖ ≤ BE0 + BE1 := fun w =>
    (clm_norm_basis _).trans (add_le_add (hBE0 w) (hBE1 w))
  obtain ⟨BΨ, hBΨ⟩ : ∃ B, ∀ w, ‖Ψ w‖ ≤ B := by
    have hΨc : Continuous Ψ := (PsiK_contDiff km).continuous.sub (PsiK_contDiff kp).continuous
    obtain ⟨B0, -, hB0⟩ := bound_closedBall 2 Ψ hΨc
    obtain ⟨C1, hC1⟩ := pba km hkm 0 2 (by norm_num)
    obtain ⟨C2, hC2⟩ := pba kp hkp 0 2 (by norm_num)
    refine ⟨max B0 (C1 + C2), fun w => ?_⟩
    by_cases hw : ‖w‖ ≤ 2
    · exact (hB0 w (by rw [mem_closedBall, dist_zero_right]; exact hw)).trans (le_max_left _ _)
    · push Not at hw
      have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
      have e := (psi_identities km kp hkm hkp 0 w hw0).1
      rw [sub_zero] at e
      show ‖PsiK km w - PsiK kp w‖ ≤ _
      rw [← e]
      refine ((norm_sub_le _ _).trans ?_).trans (le_max_right _ _)
      exact add_le_add (hC1 w (by rw [sub_zero]; exact hw.le)).1 (hC2 w (by rw [sub_zero]; exact hw.le)).1
  have hQΨ := fun z => HQ.of_global_lip f hfc α hα0 hα1.le Ψ BΨ (BE0 + BE1) (by positivity) hBΨ
    (fun x => ⟨_, hΨd x, hΨdb x⟩) z
  -- smooth far part
  obtain ⟨BF, KF, K2F, hKF, hK2F, hFb⟩ := far_part_bounds kp hkp χ hχ1 hχ2 x0 hχ3
  have hE0n : ‖E0‖ = 1 := by simp [E0]
  have hE1n : ‖E1‖ = 1 := by simp [E1]
  have hFpieces : ∀ z ∈ ball x0 (1 / 2),
      HQ f α (fun s => ((1 - χ (gpt f s) : ℝ) : ℂ) * Phi kp (gpt f s) z) BF (KF + 2 * BF) ∧
      HQ f α (fun s => fderiv ℝ (fun y => ((1 - χ y : ℝ) : ℂ) * Phi kp y z) (gpt f s) E0)
        KF (K2F + 2 * KF) ∧
      HQ f α (fun s => fderiv ℝ (fun y => ((1 - χ y : ℝ) : ℂ) * Phi kp y z) (gpt f s) E1)
        KF (K2F + 2 * KF) := by
    intro z hz
    obtain ⟨hv, hd1, hd2⟩ := hFb z hz
    have hfd : ∀ y, ‖fderiv ℝ (fun y => ((1 - χ y : ℝ) : ℂ) * Phi kp y z) y‖ ≤ KF := fun y => by
      obtain ⟨D, hD, hDb⟩ := hd1 y; rw [hD.fderiv]; exact hDb
    have hdir : ∀ e : R2, ‖e‖ = 1 → HQ f α
        (fun s => fderiv ℝ (fun y => ((1 - χ y : ℝ) : ℂ) * Phi kp y z) (gpt f s) e)
        KF (K2F + 2 * KF) := by
      intro e he
      refine (HQ.of_global_lip f hfc α hα0 hα1.le
        (fun y => fderiv ℝ (fun y => ((1 - χ y : ℝ) : ℂ) * Phi kp y z) y e) KF K2F hK2F
        (fun y => ?_) (fun y => ?_) 0).congr (fun s => by simp)
      · exact ((fderiv ℝ _ y).le_opNorm e).trans (by rw [he, mul_one]; exact hfd y)
      · obtain ⟨L, hL, hLb⟩ := hd2 e y; exact ⟨L, hL, by rw [he, mul_one] at hLb; exact hLb⟩
    refine ⟨(HQ.of_global_lip f hfc α hα0 hα1.le _ BF KF hKF hv hd1 0).congr (fun s => by simp),
      hdir E0 hE0n, hdir E1 hE1n⟩
  obtain ⟨Bd, Hd, Bc, Hc, Bq, Hq, hFd, hcinv, hq⟩ := deriv_pieces f hf α hα0 hα1.le
  set a : ℂ := ((μ⁻¹ : ℝ) : ℂ) with ha
  set c : ℂ := ((μ⁻¹ - 1 : ℝ) : ℂ) with hc
  set Fz : R2 → R2 → ℂ := fun z y => ((1 - χ y : ℝ) : ℂ) * Phi kp y z with hFz
  have hne : ∀ z, z ∈ Dplus f → ∀ s, gpt f s ≠ z := fun z hz1 s h => by
    have := hz1; rw [← h] at this; simp [Dplus, gpt, pt] at this
  have hFdiff : ∀ z ∈ ball x0 (1 / 2), ∀ y, HasFDerivAt (Fz z) (fderiv ℝ (Fz z) y) y :=
    fun z hz y => by
      obtain ⟨D, hD, -⟩ := (hFb z hz).2.1 y; exact hD.differentiableAt.hasFDerivAt
  have eG1 : ∀ z, z ∈ Dplus f → ∀ s, (fun s =>
          (incData f (pointSource kp z)).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) * Phi kp (gpt f s) z -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) z)) s =
      a * Ψ (gpt f s - z) + c * Fz z (gpt f s) := by
    intro z hz1 s
    simp only [incData, pointSource, hΨ, hFz, ha, hc]
    rw [← (psi_identities km kp hkm hkp z (gpt f s) (hne z hz1 s)).1]
    push_cast; ring
  set G1' : R2 → ℝ → ℂ := fun z s =>
    a * (gPsi km kp E0 (gpt f s - z) + ((deriv f s : ℝ) : ℂ) * gPsi km kp E1 (gpt f s - z)) +
    c * (fderiv ℝ (Fz z) (gpt f s) E0 + ((deriv f s : ℝ) : ℂ) * fderiv ℝ (Fz z) (gpt f s) E1)
    with hG1'
  have hG1d : ∀ z ∈ ball x0 (1 / 2), ∀ s,
      HasDerivAt (fun s => a * Ψ (gpt f s - z) + c * Fz z (gpt f s)) (G1' z s) s := by
    intro z hz s
    have hX := (hasDerivAt_gpt f hf.1 s).sub_const z
    have h1 := (hΨd (gpt f s - z)).comp_hasDerivAt s hX
    have h2 := (hFdiff z hz (gpt f s)).comp_hasDerivAt s (hasDerivAt_gpt f hf.1 s)
    refine ((h1.const_mul a).add (h2.const_mul c)).congr_deriv ?_
    simp only [hG1', ContinuousLinearMap.sub_apply]
    rw [pt_eq]
    simp only [map_add, map_smul, gPsi, Complex.real_smul, Complex.ofReal_one, one_mul]
    ring
  have hdiff : ∀ z, z ∈ Dplus f → z ∈ ball x0 (1 / 2) → Differentiable ℝ (fun s =>
          (incData f (pointSource kp z)).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) * Phi kp (gpt f s) z -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) z)) := by
    intro z hz1 hz2
    rw [show (fun s =>
          (incData f (pointSource kp z)).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) * Phi kp (gpt f s) z -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) z)) = fun s => a * Ψ (gpt f s - z) + c * Fz z (gpt f s) from
      funext (eG1 z hz1)]
    exact fun s => (hG1d z hz2 s).differentiableAt
  have esg : ∀ z, z ∈ Dplus f → z ∈ ball x0 (1 / 2) → ∀ s, (!₂[G1' z s * (((1 + deriv f s ^ 2)⁻¹ : ℝ) : ℂ),
      G1' z s * ((deriv f s : ℝ) : ℂ) * (((1 + deriv f s ^ 2)⁻¹ : ℝ) : ℂ)] :
        EuclideanSpace ℂ (Fin 2)) = surfGrad f (fun s =>
          (incData f (pointSource kp z)).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) * Phi kp (gpt f s) z -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) z)) s := by
    intro z hz1 hz2 s
    rw [show (fun s =>
          (incData f (pointSource kp z)).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) * Phi kp (gpt f s) z -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) z)) = fun s => a * Ψ (gpt f s - z) + c * Fz z (gpt f s) from
      funext (eG1 z hz1)]
    simp only [surfGrad, (hG1d z hz2 s).deriv]
    push_cast
    simp only [div_eq_mul_inv]
  have eG2 : ∀ z, z ∈ Dplus f → ∀ s,
      (((arcDen f s)⁻¹ : ℝ) : ℂ) * ((deriv f s : ℝ) : ℂ) * gPsi km kp E0 (gpt f s - z) +
        (-(((arcDen f s)⁻¹ : ℝ) : ℂ)) * gPsi km kp E1 (gpt f s - z) = (fun s =>
          (incData f (pointSource kp z)).2 s - 0 -
          -((μ : ℂ) * (((μ⁻¹ : ℝ) : ℂ) * fderiv ℝ (fun x => Phi km x z) (gpt f s) (normal f s)))) s := by
    intro z hz1 s
    simp only [incData]
    unfold pointSource
    have h := (psi_identities km kp hkm hkp z (gpt f s) (hne z hz1 s)).2 (normal f s)
    have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    have hμμ : (μ : ℂ) * ((μ⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast; exact mul_inv_cancel₀ hμ0
    have key : -(fderiv ℝ (fun x => Phi kp x z) (gpt f s) (normal f s)) - 0 -
        -((μ : ℂ) * (((μ⁻¹ : ℝ) : ℂ) * fderiv ℝ (fun x => Phi km x z) (gpt f s) (normal f s))) =
        gPsi km kp (normal f s) (gpt f s - z) := by
      rw [← h]
      linear_combination (fderiv ℝ (fun x => Phi km x z) (gpt f s) (normal f s)) * hμμ
    have hn : normal f s = ((arcDen f s)⁻¹ * deriv f s) • E0 + (-(arcDen f s)⁻¹) • E1 := by
      rw [normal, pt_eq, smul_add, smul_smul, smul_smul, mul_neg_one]
    rw [key, hn, gPsi_lin]
    push_cast
    ring
  have hP0 := fun z => HQ.add f α (hQ0 z) (HQ.mul f α hFd (hQ1 z))
  have hPF := fun z hz => HQ.add f α (hFpieces z hz).2.1 (HQ.mul f α hFd (hFpieces z hz).2.2)
  have hQG1' := fun z hz => HQ.add f α (HQ.mul f α (HQ.const f α a) (hP0 z))
    (HQ.mul f α (HQ.const f α c) (hPF z hz))
  obtain ⟨B1, H1, Bs, Hs, B2, H2, hclaim⟩ : ∃ B1 H1 Bs Hs B2 H2 : ℝ, ∀ z, z ∈ Dplus f →
      z ∈ ball x0 (1 / 2) →
      HQ f α (fun s =>
          (incData f (pointSource kp z)).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) * Phi kp (gpt f s) z -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) z)) B1 H1 ∧
      HQ f α (surfGrad f (fun s =>
          (incData f (pointSource kp z)).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) * Phi kp (gpt f s) z -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) z))) Bs Hs ∧ HQ f α (fun s =>
          (incData f (pointSource kp z)).2 s - 0 -
          -((μ : ℂ) * (((μ⁻¹ : ℝ) : ℂ) * fderiv ℝ (fun x => Phi km x z) (gpt f s) (normal f s)))) B2 H2 :=
    ⟨_, _, _, _, _, _, fun z hz1 hz2 =>
      ⟨HQ.congr (HQ.add f α (HQ.mul f α (HQ.const f α a) (hQΨ z))
          (HQ.mul f α (HQ.const f α c) (hFpieces z hz2).1)) (fun s => (eG1 z hz1 s).symm),
       HQ.congr (HQ.vec2 f α (HQ.mul f α (hQG1' z hz2) hcinv)
          (HQ.mul f α (HQ.mul f α (hQG1' z hz2) hFd) hcinv)) (esg z hz1 hz2),
       HQ.congr (HQ.add f α (HQ.mul f α (HQ.mul f α hq hFd) (hQ0 z))
          (HQ.mul f α (HQ.neg f α hq) (hQ1 z))) (eG2 z hz1)⟩⟩
  refine ⟨B1 + (Bs + max Hs 0) + (B2 + max H2 0), fun j hj => ?_⟩
  have hn1 := normal_norm f s0
  have hn0 : normal f s0 ≠ 0 := fun h => by rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht : 0 < δ / (j : ℝ) := by positivity
  have htle : δ / (j : ℝ) ≤ δ := div_le_self hδ.le hj'
  have hnv : ‖-((δ / (j : ℝ)) • normal f s0)‖ = δ / j := by
    rw [norm_neg, norm_smul, hn1, mul_one, Real.norm_eq_abs, abs_of_pos ht]
  have hxj : gpt f s0 - (δ / (j : ℝ)) • normal f s0 ∈ Dplus f := by
    have := hcone (-((δ / (j : ℝ)) • normal f s0))
      (by rw [neg_ne_zero]; exact smul_ne_zero ht.ne' hn0)
      (by rw [hnv]; linarith)
      (by
        rw [hnv, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq, hn1]
        simp only [one_pow, mul_one, RCLike.conj_to_real]
        linarith)
    rwa [← sub_eq_add_neg] at this
  have hxjb : gpt f s0 - (δ / (j : ℝ)) • normal f s0 ∈ ball x0 (1 / 2) := by
    rw [mem_ball, dist_eq_norm, hx0, sub_sub_cancel_left, hnv]
    linarith
  obtain ⟨h1, h3, h4⟩ := hclaim _ hxj hxjb
  have h2 := hdiff _ hxj hxjb
  refine ⟨⟨⟨h1.1, ⟨B1, h1.2.1⟩⟩, h2, HQ.isBC0 f α h3⟩, HQ.isBC0 f α h4, ?_⟩
  unfold holderNorm1
  have e1 : supNormGam _ ≤ B1 := Real.iSup_le (fun s => h1.2.1 s) (HQ.B_nonneg f α h1)
  have e2 := HQ.holderNorm0_le f α (HQ.mono f α h3 le_rfl (le_max_left Hs 0)) (le_max_right _ _)
  have e3 := HQ.holderNorm0_le f α (HQ.mono f α h4 le_rfl (le_max_left H2 0)) (le_max_right _ _)
  linarith
