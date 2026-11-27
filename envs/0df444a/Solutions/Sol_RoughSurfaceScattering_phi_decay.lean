-- Prove2me | solution 1 for RoughSurfaceScattering.phi_decay
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T02:06:34.577919+00:00
-- url     : https://prove2.me/submissions/20720d8c-6c7c-4459-8c26-078959b9fb4d

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



lemma decay_profile (G G1 : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hG : ∀ t, 0 < t → HasDerivAt G (G1 t) t)
    (hG1 : ∀ t, 0 < t → HasDerivAt G1 ((-A * G t - G1 t) / t) t) :
    ∃ M, ∀ t, 1 ≤ t → |G t| ≤ M * t ^ (-(1 / 4 : ℝ)) ∧
      |G1 t| * Real.sqrt t ≤ M * t ^ (-(1 / 4 : ℝ)) := by
  set g : ℝ → ℝ := fun r => G (r ^ 2)
  set g1 : ℝ → ℝ := fun r => 2 * r * G1 (r ^ 2)
  have hg : ∀ r, 0 < r → HasDerivAt g (g1 r) r := by
    intro r hr
    have := (hG (r ^ 2) (by positivity)).comp r (hasDerivAt_pow 2 r)
    refine this.congr_deriv ?_
    simp only [g1, Nat.cast_ofNat, pow_one]; ring
  have hg1 : ∀ r, 0 < r → HasDerivAt g1 (-(g1 r) / r - 4 * A * g r) r := by
    intro r hr
    have h1 := (hG1 (r ^ 2) (by positivity)).comp r (hasDerivAt_pow 2 r)
    have h2 := ((hasDerivAt_id r).const_mul 2).mul h1
    refine h2.congr_deriv ?_
    simp only [g1, g, id, Nat.cast_ofNat, pow_one, Function.comp_def]
    field_simp
    ring
  set u : ℝ → ℝ := fun r => Real.sqrt r * g r
  set u1 : ℝ → ℝ := fun r => g r / (2 * Real.sqrt r) + Real.sqrt r * g1 r
  have hsq : ∀ r, 0 < r → HasDerivAt Real.sqrt (1 / (2 * Real.sqrt r)) r := fun r hr => by
    simpa using Real.hasDerivAt_sqrt hr.ne'
  have hu : ∀ r, 0 < r → HasDerivAt u (u1 r) r := by
    intro r hr
    have := (hsq r hr).mul (hg r hr)
    refine this.congr_deriv ?_
    simp only [u1]; ring
  have hu1 : ∀ r, 0 < r → HasDerivAt u1 (-(4 * A + 1 / (4 * r ^ 2)) * u r) r := by
    intro r hr
    have hs := Real.sqrt_pos.mpr hr
    have hss : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    have h1 := (hg r hr).div ((hsq r hr).const_mul 2) (by positivity)
    have h2 := (hsq r hr).mul (hg1 r hr)
    refine (h1.add h2).congr_deriv ?_
    simp only [u, u1]
    field_simp
    have h2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
    have h4 : Real.sqrt r ^ 4 = r ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, h2]
    rw [h4, h2]
    ring
  set E : ℝ → ℝ := fun r => u1 r ^ 2 + (4 * A + 1 / (4 * r ^ 2)) * u r ^ 2
  have hE : ∀ r, 0 < r → HasDerivAt E (-(u r ^ 2) / (2 * r ^ 3)) r := by
    intro r hr
    have hc : HasDerivAt (fun r : ℝ => 4 * A + 1 / (4 * r ^ 2)) (-(1 / (2 * r ^ 3))) r := by
      have := ((hasDerivAt_pow 2 r).const_mul 4).inv (by positivity)
      have h := this.const_add (4 * A)
      refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
      · field_simp; ring
      · filter_upwards with s; simp [one_div]
    have := ((hu1 r hr).pow 2).add (hc.mul ((hu r hr).pow 2))
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring
  have hanti : AntitoneOn E (Set.Ici 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1) ?_ ?_ ?_
    · exact fun r hr => (hE r (lt_of_lt_of_le one_pos hr)).continuousAt.continuousWithinAt
    · intro r hr; rw [interior_Ici] at hr
      exact (hE r (lt_trans one_pos hr)).differentiableAt.differentiableWithinAt
    · intro r hr; rw [interior_Ici] at hr
      have hr0 : 0 < r := lt_trans one_pos hr
      rw [(hE r hr0).deriv]
      have : 0 ≤ u r ^ 2 / (2 * r ^ 3) := by positivity
      rw [neg_div]; linarith
  set E1 := E 1
  have hE1 : 0 ≤ E1 := by simp only [E1, E]; positivity
  set Mu := Real.sqrt (E1 / (4 * A))
  refine ⟨Mu + (Real.sqrt E1 + Mu / 2) / 2, fun t ht => ?_⟩
  set r := Real.sqrt t with hrdef
  have hr1 : 1 ≤ r := by rw [hrdef, Real.one_le_sqrt]; exact ht
  have hr0 : 0 < r := by linarith
  have hrr : r * r = t := Real.mul_self_sqrt (by linarith)
  have hEr : E r ≤ E1 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr1) hr1
  have hb1 : 4 * A * u r ^ 2 ≤ E1 := by
    have : 0 ≤ u1 r ^ 2 + 1 / (4 * r ^ 2) * u r ^ 2 := by positivity
    simp only [E] at hEr; nlinarith
  have hb2 : u1 r ^ 2 ≤ E1 := by
    have : 0 ≤ (4 * A + 1 / (4 * r ^ 2)) * u r ^ 2 := by positivity
    simp only [E] at hEr; linarith
  have hu_b : |u r| ≤ Mu := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ (by positivity)]; linarith)
  have hu1_b : |u1 r| ≤ Real.sqrt E1 := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hb2
  have hsr : Real.sqrt r = t ^ (1 / 4 : ℝ) := by
    rw [hrdef, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]; norm_num
  have hsrp : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have htm : t ^ (-(1 / 4 : ℝ)) = 1 / Real.sqrt r := by
    rw [Real.rpow_neg (by linarith), hsr]; exact (one_div _).symm
  have hgt : G t = g r := by simp only [g]; rw [hrdef, Real.sq_sqrt (by linarith)]
  have hg1t : G1 t * Real.sqrt t = g1 r / 2 := by
    simp only [g1]; rw [hrdef, Real.sq_sqrt (by linarith)]; ring
  have hgr : |g r| ≤ Mu / Real.sqrt r := by
    rw [le_div_iff₀ hsrp]
    have : |u r| = Real.sqrt r * |g r| := by
      simp only [u]; rw [abs_mul, abs_of_pos hsrp]
    linarith
  have hMu : 0 ≤ Mu := Real.sqrt_nonneg _
  have hs1 : 1 ≤ Real.sqrt r := by rw [Real.one_le_sqrt]; exact hr1
  rw [htm, hgt]
  constructor
  · calc |g r| ≤ Mu / Real.sqrt r := hgr
      _ ≤ (Mu + (Real.sqrt E1 + Mu / 2) / 2) * (1 / Real.sqrt r) := by
          rw [div_eq_mul_one_div]
          gcongr
          have : 0 ≤ (Real.sqrt E1 + Mu / 2) / 2 := by positivity
          linarith
  · rw [show |G1 t| * Real.sqrt t = |G1 t * Real.sqrt t| by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)], hg1t]
    have hu1e : g1 r = (u1 r - g r / (2 * Real.sqrt r)) / Real.sqrt r := by
      simp only [u1]; field_simp; ring
    have h2 : |g r / (2 * Real.sqrt r)| ≤ Mu / 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt r), div_le_div_iff₀
        (by positivity) (by norm_num)]
      have := hgr; rw [le_div_iff₀ hsrp] at this
      nlinarith [mul_le_mul_of_nonneg_left hs1 (abs_nonneg (g r)), mul_le_mul_of_nonneg_left hs1 hMu]
    rw [hu1e, abs_div, abs_div, abs_of_pos hsrp, abs_two]
    have h3 : |u1 r - g r / (2 * Real.sqrt r)| ≤ Real.sqrt E1 + Mu / 2 :=
      (abs_sub _ _).trans (add_le_add hu1_b h2)
    calc |u1 r - g r / (2 * Real.sqrt r)| / Real.sqrt r / 2 ≤
        (Real.sqrt E1 + Mu / 2) / Real.sqrt r / 2 := by gcongr
      _ ≤ (Mu + (Real.sqrt E1 + Mu / 2) / 2) * (1 / Real.sqrt r) := by
          rw [div_div, mul_one_div, div_le_div_iff₀ (by positivity) hsrp]
          nlinarith [Real.sqrt_nonneg E1]



theorem solution (k : ℝ) (hk : 0 < k) :
    ∃ C : ℝ, ∀ z x : R2, 1 ≤ ‖x - z‖ →
      ‖Phi k x z‖ ≤ C * ‖x - z‖ ^ (-(1 / 2 : ℝ)) ∧
      ‖fderiv ℝ (fun x' => Phi k x' z) x‖ ≤ C * ‖x - z‖ ^ (-(1 / 2 : ℝ)) := by
  set A : ℝ := k ^ 2 / 4
  have hA : 0 < A := by positivity
  set β : ℂ := Complex.I / 4 -
    (((Real.log (k / 2) + Real.eulerMascheroniConstant) / (2 * Real.pi) : ℝ) : ℂ)
  have hR2 : ∀ t, 0 < t → HasDerivAt (R1t A) ((-A * Rt A t - R1t A t) / t) t := by
    intro t ht
    have hg := (R1t_diff A t ht).hasDerivAt
    have hrel : -A * Rt A t = R1t A t + t * deriv (R1t A) t := by
      have := (hasDerivAt_id t).mul hg
      simp only [id, one_mul] at this
      exact (ode_Rt A t ht).unique this
    refine hg.congr_deriv ?_
    field_simp; linarith
  have hJ2 : ∀ t, 0 < t → HasDerivAt (J1t A) ((-A * Jt A t - J1t A t) / t) t := by
    intro t ht
    have hg := (J1t_diff A t).hasDerivAt
    have hrel : -A * Jt A t = J1t A t + t * deriv (J1t A) t := by
      have := (hasDerivAt_id t).mul hg
      simp only [id, one_mul] at this
      exact (ode_Jt A t).unique this
    refine hg.congr_deriv ?_
    field_simp; linarith
  obtain ⟨MR, hMR⟩ := decay_profile (Rt A) (R1t A) A hA (fun t ht => hasDerivAt_Rt A t ht.ne') hR2
  obtain ⟨MJ, hMJ⟩ := decay_profile (Jt A) (J1t A) A hA (fun t _ => hasDerivAt_Jt A t) hJ2
  have hMR0 : 0 ≤ MR := by
    have := (hMR 1 le_rfl).1; rw [Real.one_rpow, mul_one] at this; exact (abs_nonneg _).trans this
  have hMJ0 : 0 ≤ MJ := by
    have := (hMJ 1 le_rfl).1; rw [Real.one_rpow, mul_one] at this; exact (abs_nonneg _).trans this
  refine ⟨2 * (MR + ‖β‖ * MJ), fun z x hx => ?_⟩
  have hxz : x ≠ z := by
    intro h; rw [h, sub_self, norm_zero] at hx; linarith
  set t := ‖x - z‖ ^ 2 with htdef
  have ht1 : 1 ≤ t := by rw [htdef]; nlinarith
  have htpos : 0 < t := by linarith
  have hsq : Real.sqrt t = ‖x - z‖ := by rw [htdef, Real.sqrt_sq (norm_nonneg _)]
  have hrt : t ^ (-(1 / 4 : ℝ)) = ‖x - z‖ ^ (-(1 / 2 : ℝ)) := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num
  have hloc : (fun y => Phi k y z) =ᶠ[𝓝 x]
      fun y => ((Rt A (‖y - z‖ ^ 2) : ℝ) : ℂ) + β * ((Jt A (‖y - z‖ ^ 2) : ℝ) : ℂ) := by
    filter_upwards [isOpen_ne.mem_nhds hxz] with y hy
    rw [phi_decomp k hk y z hy, aF_eq, phi0_eq]
    simp only [bF, Rt, Jt, ell, β, A]
    have htq : tq k (y - z) = k ^ 2 / 4 * ‖y - z‖ ^ 2 := by unfold tq; ring
    rw [htq, ← Qs_eq]
    push_cast
    ring
  obtain ⟨hR1, hR2'⟩ := hMR t ht1
  obtain ⟨hJ1, hJ2'⟩ := hMJ t ht1
  rw [hrt] at hR1 hR2' hJ1 hJ2'
  have hβ := norm_nonneg β
  have hp : 0 ≤ ‖x - z‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  constructor
  · rw [hloc.eq_of_nhds]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hJ1 hβ
    nlinarith [mul_nonneg hMR0 hp, mul_nonneg (mul_nonneg hβ hMJ0) hp]
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
    rw [hsq] at hR2' hJ2'
    rw [show |2 * @inner ℝ R2 _ (x - z) v| = 2 * |@inner ℝ R2 _ (x - z) v| by
      rw [abs_mul, abs_two]]
    have e1 : |R1t A t| * (2 * |@inner ℝ R2 _ (x - z) v|) ≤
        2 * (MR * ‖x - z‖ ^ (-(1 / 2 : ℝ))) * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left hin (abs_nonneg (R1t A t))
      nlinarith
    have e2 : |J1t A t| * (2 * |@inner ℝ R2 _ (x - z) v|) ≤
        2 * (MJ * ‖x - z‖ ^ (-(1 / 2 : ℝ))) * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left hin (abs_nonneg (J1t A t))
      nlinarith
    have := mul_le_mul_of_nonneg_left e2 hβ
    nlinarith [mul_nonneg (mul_nonneg hMR0 hp) hv, mul_nonneg (mul_nonneg (mul_nonneg hβ hMJ0) hp) hv]
