-- Prove2me | solution 1 for RoughSurfaceScattering.fundamental_solution_difference_regular
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T16:46:10.220921+00:00
-- url     : https://prove2.me/submissions/9696cd8b-d8a7-472c-be97-4600e6b26783

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Metric Filter Topology
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



lemma memLp_of_continuous_ball (y : R2) (f : R2 → ℂ) (hf : Continuous f) (p : ENNReal) :
    MemLp f p (volume.restrict (ball y 1)) := by
  haveI : IsFiniteMeasure (volume.restrict (ball y 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_closedBall y 1).exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_ball fun x hx => hC x (ball_subset_closedBall hx))

lemma bound_on_closedBall {E : Type*} [NormedAddCommGroup E] (f : R2 → E) (hf : Continuous f) :
    ∃ M ≥ (0 : ℝ), ∀ w ∈ closedBall (0 : R2) 1, ‖f w‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : R2) 1).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun w hw => (hC w hw).trans (le_max_left _ _)⟩

theorem solution (y : R2) (k k1 : ℝ) (hk : 0 ≤ k) (hk1 : 0 ≤ k1)
    (p : ENNReal) (hp1 : 1 ≤ p) (hp : p ≠ ⊤) :
    ∃ Dt : R2 → ℂ, (∀ x, x ≠ y → Dt x = Phi k1 x y - Phi k x y) ∧
      ContDiffOn ℝ 1 Dt (Metric.ball y 1) ∧
      (∀ i : Fin 2, ∀ x ∈ Metric.ball y 1, x ≠ y →
        DifferentiableAt ℝ (fun z => fderiv ℝ Dt z (EuclideanSpace.single i 1)) x) ∧
      MemLp Dt p (volume.restrict (Metric.ball y 1)) ∧
      (∀ i : Fin 2, MemLp (fun x => fderiv ℝ Dt x (EuclideanSpace.single i 1)) p
        (volume.restrict (Metric.ball y 1))) ∧
      (∀ i j : Fin 2, MemLp (fun x => fderiv ℝ (fun z => fderiv ℝ Dt z (EuclideanSpace.single i 1))
        x (EuclideanSpace.single j 1)) p (volume.restrict (Metric.ball y 1))) := by
  set c : ℝ := -(1 / (4 * Real.pi)) with hc
  set Q : R2 → ℝ := fun w => qJ (k1 ^ 2 / 4) (k ^ 2 / 4) (‖w‖ ^ 2) with hQdef
  have hQ : ContDiff ℝ 2 Q := (contDiff_qJ _ _).comp (contDiff_norm_sq ℝ)
  set F : R2 → ℝ := fun w => Q w * Lam w with hFdef
  have hF : ContDiff ℝ 1 F := (hQ.of_le (by norm_num)).mul Lam_contDiff
  set Bd : R2 → ℂ := fun w => bG k1 w - bG k w with hBddef
  have hBd : ContDiff ℝ 2 Bd := (contDiff_bG k1).sub (contDiff_bG k)
  set Ψ : R2 → ℂ := fun w => ((c * F w : ℝ) : ℂ) + Bd w with hΨdef
  have hΨ : ContDiff ℝ 1 Ψ :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hF)).add (hBd.of_le (by norm_num))
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hBdd : Differentiable ℝ Bd := hBd.differentiable (by norm_num)
  have hBd1 : ContDiff ℝ 1 (fderiv ℝ Bd) := hBd.fderiv_right (by norm_num)
  -- directional first derivative of `Ψ`
  have hΨfd : ∀ (w e : R2), fderiv ℝ Ψ w e = ((c * fderiv ℝ F w e : ℝ) : ℂ) + fderiv ℝ Bd w e := by
    intro w e
    have h := (Complex.ofRealCLM.hasFDerivAt.comp w ((hFd w).hasFDerivAt.const_mul c)).add
      (hBdd w).hasFDerivAt
    rw [show Ψ = (⇑Complex.ofRealCLM ∘ fun y => c * F y) + Bd from rfl, h.fderiv]
    simp
  -- second derivative of `Ψ` off the origin
  obtain ⟨M, hM0, hM⟩ := bound_on_closedBall (fun w => (Q w, fderiv ℝ Q w, fderiv ℝ (fderiv ℝ Q) w))
    (hQ.continuous.prodMk ((hQ.continuous_fderiv (by norm_num)).prodMk
      ((hQ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero)))
  obtain ⟨ML, hML0, hML⟩ := bound_on_closedBall (fun w => (Lam w, Lam' w))
    (Lam_contDiff.continuous.prodMk Lam'_continuous)
  obtain ⟨MB, hMB0, hMB⟩ := bound_on_closedBall (fderiv ℝ (fderiv ℝ Bd))
    (hBd1.continuous_fderiv one_ne_zero)
  set K : ℝ := |c| * (6 * M + 3 * M * ML) + MB + 4 * |c| * M with hK
  have hsecond : ∀ (e : R2), ‖e‖ = 1 → ∀ w : R2, w ≠ 0 → ‖w‖ < 1 →
      ∃ G : R2 →L[ℝ] ℂ, HasFDerivAt (fun z => fderiv ℝ Ψ z e) G w ∧
        ‖G‖ ≤ K * (1 + |Real.log ‖w‖|) := by
    intro e he w hw hw1
    obtain ⟨D, hD, hDb⟩ := QLam_second Q hQ w hw
    have h1 : HasFDerivAt (fun z => fderiv ℝ F z e) ((ContinuousLinearMap.apply ℝ ℝ e).comp D) w :=
      (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp w hD
    have h2 : HasFDerivAt (fun z => fderiv ℝ Bd z e)
        ((ContinuousLinearMap.apply ℝ ℂ e).comp (fderiv ℝ (fderiv ℝ Bd) w)) w :=
      (ContinuousLinearMap.apply ℝ ℂ e).hasFDerivAt.comp w
        ((hBd1.differentiable one_ne_zero) w).hasFDerivAt
    have h3 := (Complex.ofRealCLM.hasFDerivAt.comp w (h1.const_mul c)).add h2
    have heq : (fun z => fderiv ℝ Ψ z e) =
        fun z => Complex.ofRealCLM (c * fderiv ℝ F z e) + fderiv ℝ Bd z e := by
      funext z; rw [hΨfd]; rfl
    rw [heq]
    refine ⟨_, h3, ?_⟩
    have hwB : w ∈ closedBall (0 : R2) 1 := by rw [mem_closedBall, dist_zero_right]; exact hw1.le
    have hMw := hM w hwB
    have hMLw := hML w hwB
    have hQw : |Q w| ≤ M := by
      rw [← Real.norm_eq_abs]; exact (norm_fst_le _).trans hMw
    have hQ1w : ‖fderiv ℝ Q w‖ ≤ M := ((norm_fst_le _).trans (norm_snd_le _)).trans hMw
    have hQ2w : ‖fderiv ℝ (fderiv ℝ Q) w‖ ≤ M :=
      ((norm_snd_le _).trans (norm_snd_le _)).trans hMw
    have hLw : |Lam w| ≤ ML := by rw [← Real.norm_eq_abs]; exact (norm_fst_le _).trans hMLw
    have hL1w : ‖Lam' w‖ ≤ ML := (norm_snd_le _).trans hMLw
    have hlog : |Real.log (‖w‖ ^ 2) + 1| ≤ 2 * |Real.log ‖w‖| + 1 := by
      rw [Real.log_pow]; push_cast
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two, abs_one]
    have hDb' : ‖D‖ ≤ M * (4 * |Real.log ‖w‖| + 6) + 3 * M * ML := by
      refine hDb.trans ?_
      have := abs_nonneg (Real.log ‖w‖)
      calc _ ≤ M * (2 * (2 * |Real.log ‖w‖| + 1) + 4) + 2 * M * ML + ML * M := by
            gcongr
      _ = _ := by ring
    have hBw := hMB w hwB
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, Complex.ofRealCLM_apply]
    have e1 : (c • (ContinuousLinearMap.apply ℝ ℝ e).comp D) u = c * D u e := by simp
    rw [e1]
    have a1 := D.le_opNorm₂ u e
    have a2 := (fderiv ℝ (fderiv ℝ Bd) w).le_opNorm₂ u e
    rw [he, mul_one] at a1 a2
    rw [Real.norm_eq_abs] at a1
    have hu := norm_nonneg u
    have hL := abs_nonneg (Real.log ‖w‖)
    have hc0 := abs_nonneg c
    calc _ ≤ ‖((c * D u e : ℝ) : ℂ)‖ + ‖fderiv ℝ (fderiv ℝ Bd) w u e‖ := norm_add_le _ _
      _ ≤ |c| * (‖D‖ * ‖u‖) + MB * ‖u‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
          gcongr
          exact a2.trans (by gcongr)
      _ ≤ |c| * ((M * (4 * |Real.log ‖w‖| + 6) + 3 * M * ML) * ‖u‖) + MB * ‖u‖ := by gcongr
      _ ≤ _ := by
          rw [hK]
          have : 0 ≤ (|c| * (6 * M + 3 * M * ML) + MB) * |Real.log ‖w‖| * ‖u‖ := by positivity
          have h4 : 0 ≤ 4 * |c| * M * ‖u‖ := by positivity
          have : (|c| * (6 * M + 3 * M * ML) + MB + 4 * |c| * M) * (1 + |Real.log ‖w‖|) * ‖u‖ -
              (|c| * ((M * (4 * |Real.log ‖w‖| + 6) + 3 * M * ML) * ‖u‖) + MB * ‖u‖) =
              4 * |c| * M * ‖u‖ + (|c| * (6 * M + 3 * M * ML) + MB) * |Real.log ‖w‖| * ‖u‖ := by ring
          linarith
  have hsingle : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : R2)‖ = 1 := fun i => by
    simp [EuclideanSpace.norm_single]
  have hfdDt : ∀ e : R2, (fun z => fderiv ℝ (fun x => Ψ (x - y)) z e) =
      fun z => fderiv ℝ Ψ (z - y) e := fun e => by
    funext z; rw [fderiv_comp_sub (f := Ψ) y]
  have hsec' : ∀ i : Fin 2, ∀ x ∈ ball y 1, x ≠ y → ∃ G : R2 →L[ℝ] ℂ,
      HasFDerivAt (fun z => fderiv ℝ Ψ (z - y) (EuclideanSpace.single i 1)) G x ∧
        ‖G‖ ≤ K * (1 + |Real.log ‖x - y‖|) := by
    intro i x hx hxy
    have hw1 : ‖x - y‖ < 1 := by rw [mem_ball, dist_eq_norm] at hx; exact hx
    obtain ⟨G, hG, hGb⟩ := hsecond _ (hsingle i) (x - y) (sub_ne_zero.mpr hxy) hw1
    have := hG.comp x ((hasFDerivAt_id x).sub_const y)
    refine ⟨_, this, ?_⟩
    simpa using hGb
  refine ⟨fun x => Ψ (x - y), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (phi_diff_eq k k1 hk hk1 x y hx).symm
  · exact (hΨ.comp (contDiff_id.sub contDiff_const)).contDiffOn
  · intro i x hx hxy
    rw [hfdDt]
    obtain ⟨G, hG, -⟩ := hsec' i x hx hxy
    exact hG.differentiableAt
  · exact memLp_of_continuous_ball y _ (hΨ.continuous.comp (continuous_sub_right y)) p
  · intro i
    rw [hfdDt]
    exact memLp_of_continuous_ball y _
      (((hΨ.continuous_fderiv one_ne_zero).comp (continuous_sub_right y)).clm_apply
        continuous_const) p
  · intro i j
    refine memLp_log_bound y _ K p hp1 hp
      (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable fun x hx hxy => ?_
    rw [hfdDt]
    obtain ⟨G, hG, hGb⟩ := hsec' i x hx hxy
    rw [hG.fderiv]
    exact (G.le_opNorm _).trans (by rw [hsingle, mul_one]; exact hGb)
