-- Prove2me | solution 1 for RoughSurfaceScattering.dipole_diff_h1_uniform
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T01:13:42.031594+00:00
-- url     : https://prove2.me/submissions/7d82bbd4-bfab-42da-a4ca-79f25a2419b6

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

theorem dcd_aux (k : ℝ) (hk : 0 ≤ k) (z ν : R2) :
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



lemma logsq_bound (R : ℝ) (hR : 1 ≤ R) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    (1 + |Real.log r|) ^ 2 ≤ (9 + (1 + R) ^ 2 * R) * r ^ (-1 : ℝ) := by
  rw [Real.rpow_neg_one]
  have hA : 0 ≤ (1 + R) ^ 2 * R * r⁻¹ := by positivity
  rcases lt_or_ge r 1 with h1 | h1
  · have hl := Real.abs_log_mul_self_rpow_lt r (1 / 2) hr h1.le (by norm_num)
    rw [← Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hl
    norm_num at hl
    set s := Real.sqrt r with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hr
    have hs1 : s ≤ 1 := by rw [hs]; exact Real.sqrt_le_one.mpr h1.le
    have hss : s ^ 2 = r := Real.sq_sqrt hr.le
    have hlog : |Real.log r| ≤ 2 / s := by rw [le_div_iff₀ hs0]; linarith
    have h3 : 1 + |Real.log r| ≤ 3 / s := by
      have : 1 ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
      calc 1 + |Real.log r| ≤ 1 / s + 2 / s := by linarith
        _ = 3 / s := by ring
    have h9 : (1 + |Real.log r|) ^ 2 ≤ 9 * r⁻¹ := by
      calc (1 + |Real.log r|) ^ 2 ≤ (3 / s) ^ 2 := by gcongr
        _ = 9 * r⁻¹ := by rw [← hss]; field_simp; ring
    nlinarith
  · have hlog : |Real.log r| ≤ r - 1 := by
      rw [abs_of_nonneg (Real.log_nonneg h1)]; exact Real.log_le_sub_one_of_pos hr
    have h2 : (1 + |Real.log r|) ^ 2 ≤ R ^ 2 := by
      have : 0 ≤ 1 + |Real.log r| := by positivity
      nlinarith
    have h3 : R ^ 2 ≤ (1 + R) ^ 2 * R * r⁻¹ := by
      have hri : R⁻¹ ≤ r⁻¹ := inv_anti₀ hr hrR
      have : (1 + R) ^ 2 * R * R⁻¹ = (1 + R) ^ 2 := by field_simp
      have hRp : 0 < R := by linarith
      calc R ^ 2 ≤ (1 + R) ^ 2 := by nlinarith
        _ = (1 + R) ^ 2 * R * R⁻¹ := this.symm
        _ ≤ (1 + R) ^ 2 * R * r⁻¹ := by gcongr
    have : 0 ≤ 9 * r⁻¹ := by positivity
    nlinarith

lemma lintegral_ball_translate (φ : R2 → ENNReal) (z : R2) (ρ : ℝ) :
    ∫⁻ x in ball z ρ, φ (x - z) = ∫⁻ w in ball 0 ρ, φ w := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  have e : (ball z ρ).indicator (fun x => φ (x - z)) =
      fun x => (ball (0 : R2) ρ).indicator φ (x - z) := by
    funext x
    simp only [Set.indicator, mem_ball, dist_eq_norm, sub_zero]
  rw [e, lintegral_sub_right_eq_self (fun w => (ball (0 : R2) ρ).indicator φ w) z]

theorem solution (k : ℝ) (hk : 0 ≤ k) (ν : R2) (D0 : Set R2) (hD : IsOpen D0)
    (hb : Bornology.IsBounded D0) (z0 : R2) (a : ℂ) :
    ∃ C : ℝ, ∀ z ∈ Metric.ball z0 1,
      h1Norm D0 (fun x => a * (dipoleSource k z ν x - dipoleSource 0 z ν x)) ≤
        ENNReal.ofReal C := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  set R' := max (R + ‖z0‖ + 1) 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hΨ := PsiK_contDiff k
  obtain ⟨M1, hM10, hM1⟩ := bound_closedBall R' (fderiv ℝ (PsiK k))
    (hΨ.continuous_fderiv one_ne_zero)
  obtain ⟨K, hK0, hK⟩ := PsiK_second k R'
  set Cl := 9 + (1 + R') ^ 2 * R'
  set B1 := ‖a‖ * (M1 * ‖ν‖)
  set A2 := (‖a‖ * K * ‖ν‖) ^ 2 * Cl
  set I0 := ∫⁻ w in ball (0 : R2) R', ENNReal.ofReal (A2 * ‖w‖ ^ (-1 : ℝ))
  have hint : IntegrableOn (fun w : R2 => ‖w‖ ^ (-1 : ℝ)) (ball 0 R') := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := 1)
      (by simp [finrank_euclideanSpace]) (by simp [finrank_euclideanSpace])
      (Eventually.of_forall fun w => ?_) ?_
    · rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  have hI0 : I0 ≠ ⊤ := (Integrable.lintegral_lt_top (hint.const_mul A2)).ne
  set T := ENNReal.ofReal B1 ^ 2 * volume D0 + 2 * I0
  have hV : volume D0 ≠ ⊤ := hb.measure_lt_top.ne
  have hT : T ≠ ⊤ := by
    simp only [T]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hV, ENNReal.mul_ne_top (by simp) hI0⟩
  have hfin : T ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hT
  refine ⟨(T ^ (1 / 2 : ℝ)).toReal, fun z hz => ?_⟩
  rw [ENNReal.ofReal_toReal hfin]
  unfold h1Norm
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hDsub : D0 ⊆ ball z R' := by
    intro x hx
    have h1 : ‖x‖ < R := by have := hR hx; rwa [mem_ball, dist_zero_right] at this
    have h2 : ‖z‖ < ‖z0‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z z0
      rw [mem_ball, dist_eq_norm] at hz; linarith
    rw [mem_ball, dist_eq_norm]
    have := norm_sub_le x z
    have : R + ‖z0‖ + 1 ≤ R' := le_max_left _ _
    linarith
  set φ : R2 → ENNReal := fun w => ENNReal.ofReal (A2 * ‖w‖ ^ (-1 : ℝ))
  have hstep : ∫⁻ x in D0, (ENNReal.ofReal B1 ^ 2 + 2 * φ (x - z)) ≤ T := by
    rw [lintegral_add_left measurable_const, setLIntegral_const,
      lintegral_const_mul' _ _ (by simp)]
    simp only [T]
    gcongr
    calc ∫⁻ x in D0, φ (x - z) ≤ ∫⁻ x in ball z R', φ (x - z) := lintegral_mono_set hDsub
      _ = I0 := lintegral_ball_translate φ z R'
  refine le_trans (lintegral_mono_ae ?_) hstep
  have hne : ∀ᵐ x ∂(volume.restrict D0), x ≠ z := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton z
  filter_upwards [hne, ae_restrict_mem hD.measurableSet] with x hxz hx
  set w := x - z with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hxz
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwR : ‖w‖ ≤ R' := by
    have := hDsub hx; rw [mem_ball, dist_eq_norm] at this; exact this.le
  have hwB : w ∈ closedBall (0 : R2) R' := by rw [mem_closedBall, dist_zero_right]; exact hwR
  -- the dipole difference near a point `y ≠ z`
  have hdip : ∀ y, y ≠ z → dipoleSource k z ν y - dipoleSource 0 z ν y =
      fderiv ℝ (PsiK k) (y - z) ν := by
    intro y hy
    have hdk : DifferentiableAt ℝ (fun x' => Phi k x' z) y :=
      ((phi_contDiffOn2 k hk z).differentiableOn (by norm_num) y hy).differentiableAt
        (isOpen_ne.mem_nhds hy)
    have hd0 : DifferentiableAt ℝ (fun x' => Phi 0 x' z) y :=
      ((phi_contDiffOn2 0 le_rfl z).differentiableOn (by norm_num) y hy).differentiableAt
        (isOpen_ne.mem_nhds hy)
    unfold dipoleSource
    rw [← ContinuousLinearMap.sub_apply, ← fderiv_fun_sub hdk hd0]
    have hev : (fun x' => Phi k x' z - Phi 0 x' z) =ᶠ[𝓝 y] fun x' => PsiK k (x' - z) := by
      filter_upwards [isOpen_ne.mem_nhds hy] with x' hx'
      exact PsiK_eq k hk x' z hx'
    rw [hev.fderiv_eq, fderiv_comp_sub (f := PsiK k) z]
  have hloc : (fun y => a * (dipoleSource k z ν y - dipoleSource 0 z ν y)) =ᶠ[𝓝 x]
      fun y => a * fderiv ℝ (PsiK k) (y - z) ν := by
    filter_upwards [isOpen_ne.mem_nhds hxz] with y hy
    rw [hdip y hy]
  obtain ⟨G, hG, hGb⟩ := hK ν w hw0 hwR
  have hG' : HasFDerivAt (fun y => a * fderiv ℝ (PsiK k) (y - z) ν)
      (a • (G.comp (ContinuousLinearMap.id ℝ R2))) x :=
    (hG.comp x ((hasFDerivAt_id x).sub_const z)).const_mul a
  have hval : ‖a * (dipoleSource k z ν x - dipoleSource 0 z ν x)‖ ≤ B1 := by
    rw [hdip x hxz, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact ((fderiv ℝ (PsiK k) w).le_opNorm ν).trans
      (mul_le_mul_of_nonneg_right (hM1 w hwB) (norm_nonneg _))
  have hlogb := logsq_bound R' hR'1 ‖w‖ hwpos hwR
  have hder : ∀ i : Fin 2,
      ‖fderiv ℝ (fun x => a * (dipoleSource k z ν x - dipoleSource 0 z ν x)) x
        (EuclideanSpace.single i 1)‖ ^ 2 ≤ A2 * ‖w‖ ^ (-1 : ℝ) := by
    intro i
    rw [hloc.fderiv_eq, hG'.fderiv]
    have h1 : ‖(a • (G.comp (ContinuousLinearMap.id ℝ R2))) (EuclideanSpace.single i 1)‖ ≤
        ‖a‖ * (K * (1 + |Real.log ‖w‖|) * ‖ν‖) := by
      rw [ContinuousLinearMap.smul_apply, norm_smul, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (G.le_opNorm _).trans ?_
      rw [EuclideanSpace.norm_single, norm_one, mul_one]
      exact hGb
    have h0 : 0 ≤ ‖(a • (G.comp (ContinuousLinearMap.id ℝ R2))) (EuclideanSpace.single i 1)‖ :=
      norm_nonneg _
    calc _ ≤ (‖a‖ * (K * (1 + |Real.log ‖w‖|) * ‖ν‖)) ^ 2 := by gcongr
      _ = (‖a‖ * K * ‖ν‖) ^ 2 * (1 + |Real.log ‖w‖|) ^ 2 := by ring
      _ ≤ (‖a‖ * K * ‖ν‖) ^ 2 * (Cl * ‖w‖ ^ (-1 : ℝ)) := by gcongr
      _ = _ := by simp only [A2]; ring
  have e1 : ∀ y : ℂ, ‖y‖ ≤ B1 → ‖y‖ₑ ^ 2 ≤ ENNReal.ofReal B1 ^ 2 := fun y hy => by
    rw [← ofReal_norm_eq_enorm]; gcongr
  have e2 : ∀ y : ℂ, ‖y‖ ^ 2 ≤ A2 * ‖w‖ ^ (-1 : ℝ) → ‖y‖ₑ ^ 2 ≤ φ w := fun y hy => by
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hy
  calc _ ≤ ENNReal.ofReal B1 ^ 2 + φ w + φ w :=
        add_le_add (add_le_add (e1 _ hval) (e2 _ (hder 0))) (e2 _ (hder 1))
    _ = ENNReal.ofReal B1 ^ 2 + 2 * φ (x - z) := by rw [two_mul, ← hw]; ring
