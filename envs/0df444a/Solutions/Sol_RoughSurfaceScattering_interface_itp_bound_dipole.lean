-- Prove2me | solution 1 for RoughSurfaceScattering.interface_itp_bound_dipole
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T02:49:29.684344+00:00
-- url     : https://prove2.me/submissions/85e9d4db-a841-4f7e-b32e-4f414054d820
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_h1Norm_sub_le
import Theorems.Thm_RoughSurfaceScattering_dipole_away_h1
import Theorems.Thm_RoughSurfaceScattering_itp_small_domain_l2_local
import Theorems.Thm_RoughSurfaceScattering_dipole_upper_agree_cross
import Theorems.Thm_RoughSurfaceScattering_dipole_away_bound
import Theorems.Thm_RoughSurfaceScattering_dipole_scattered_local_bound
import Theorems.Thm_RoughSurfaceScattering_dipole_helmholtz
import Theorems.Thm_RoughSurfaceScattering_dipole_tsp_exists

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

theorem dcd (k : ℝ) (hk : 0 ≤ k) (z ν : R2) :
    ContDiffOn ℝ 1 (dipoleSource k z ν) {x | x ≠ z} := by
  have hU : IsOpen {x : R2 | x ≠ z} := isOpen_ne
  have h := (phi_contDiffOn2 k hk z).fderiv_of_isOpen hU (m := 1) (by norm_num)
  exact h.clm_apply contDiffOn_const


noncomputable abbrev e2i : R2 := EuclideanSpace.single 1 1

lemma curve_apply_i (f : ℝ → ℝ) (s t : ℝ) :
    (gpt f s + t • e2i) 0 = s ∧ (gpt f s + t • e2i) 1 = f s + t := by
  simp [gpt, pt, e2i]

lemma tendsto_curve_i (f : ℝ → ℝ) (s : ℝ) :
    Tendsto (fun t : ℝ => gpt f s + t • e2i) (𝓝[>] 0) (𝓝 (gpt f s)) := by
  have h : Continuous fun t : ℝ => gpt f s + t • e2i := by fun_prop
  have := h.tendsto 0
  simp only [zero_smul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma closure_Dminus_sub_i (f : ℝ → ℝ) (hfc : Continuous f) :
    closure (Dminus f) ⊆ {x : R2 | x 1 ≤ f (x 0)} :=
  closure_minimal (fun x (hx : x 1 < f (x 0)) => (le_of_lt hx : x 1 ≤ f (x 0)))
    (isClosed_le (by fun_prop) (hfc.comp (by fun_prop)))

lemma interior_closure_Dminus_i (f : ℝ → ℝ) (hfc : Continuous f) :
    interior (closure (Dminus f)) ⊆ Dminus f := by
  intro x hx
  by_contra hxm
  have hle : x 1 ≤ f (x 0) := closure_Dminus_sub_i f hfc (interior_subset hx)
  have heq : x 1 = f (x 0) := le_antisymm hle (not_lt.mp hxm)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hy : x + (ε / 2) • e2i ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    simp [e2i]; linarith
  have h1 := closure_Dminus_sub_i f hfc (interior_subset (hball hy))
  simp [e2i] at h1
  linarith

/-- The Cauchy data of the lower field on `Γ` are those of any `C¹` function `W` that agrees
with the upper total field `uⁱ + u₊` above `Γ`. -/
lemma cross_upper (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp k μ : ℝ) (ui up um : R2 → ℂ)
    (hu : IsTSPSolution f kp k μ (incData f ui).1 (incData f ui).2 up um)
    (O : Set R2) (hO : IsOpen O) (W : R2 → ℂ) (hui : ContDiffOn ℝ 1 ui O)
    (hW : ContDiffOn ℝ 1 W O) (hag : ∀ x ∈ O ∩ Dplus f, W x = ui x + up x) :
    ∃ DV : R2 → (R2 →L[ℝ] ℂ), IsC1On (closure (Dminus f)) um DV ∧
      ∀ s, gpt f s ∈ O → um (gpt f s) = W (gpt f s) ∧
        (μ : ℂ) * DV (gpt f s) (normal f s) = fderiv ℝ W (gpt f s) (normal f s) := by
  classical
  have hfc : Continuous f := hf.1.continuous
  obtain ⟨Cf, hCf⟩ := hf.2.2.1
  have hbB : BddBelow (Set.range f) := ⟨-Cf, by
    rintro _ ⟨t, rfl⟩; have := neg_abs_le (f t); linarith [hCf t]⟩
  have hbA : BddAbove (Set.range f) := ⟨Cf, by
    rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (hCf t)⟩
  have hfi : ∀ t, finf f ≤ f t := fun t => ciInf_le hbB t
  have hfs : ∀ t, f t ≤ fsup f := fun t => le_ciSup hbA t
  obtain ⟨hp, hm, Dup, Dum, hhp, hhm, -, humC, hBCp, hBCm, -, -, ht1, ht2, -⟩ := hu
  refine ⟨fun x => if x ∈ Dminus f then fderiv ℝ um x else Dum x, ?_, fun s hsO => ?_⟩
  · have hnear : ∀ x ∈ closure (Dminus f), x ∉ Dminus f →
        {y : R2 | hm < y 1} ∈ 𝓝 x := by
      intro x hx hxm
      have hle := closure_Dminus_sub_i f hfc hx
      have heq : x 1 = f (x 0) := le_antisymm hle (not_lt.mp hxm)
      have : hm < x 1 := by rw [heq]; linarith [hfi (x 0)]
      exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds this
    have hstrip : ∀ y ∈ closure (Dminus f), hm < y 1 → y ∈ stripMinus f hm := fun y hy h =>
      ⟨hy, fun h' => by simp only [Uminus, Set.mem_setOf_eq] at h'; linarith⟩
    have hint : ∀ y ∈ Dminus f, hm < y 1 → y ∈ interior (stripMinus f hm) := by
      intro y hy h
      have hO' : IsOpen (Dminus f ∩ {y : R2 | hm < y 1}) :=
        (isOpen_lt (by fun_prop) (hfc.comp (by fun_prop))).inter
          (isOpen_lt continuous_const (by fun_prop))
      exact interior_maximal (fun z hz => hstrip z (subset_closure hz.1) hz.2) hO' ⟨hy, h⟩
    have hDmO : IsOpen (Dminus f) := isOpen_lt (by fun_prop) (hfc.comp (by fun_prop))
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · by_cases hxm : x ∈ Dminus f
      · exact ((humC.continuousOn x hxm).continuousAt (hDmO.mem_nhds hxm)).continuousWithinAt
      · have hcw := hBCm.1.1 x (hstrip x hx
          (mem_of_mem_nhds (hnear x hx hxm) : x ∈ {y : R2 | hm < y 1}))
        exact hcw.mono_of_mem_nhdsWithin (by
          filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hnear x hx hxm)]
            with y hy1 hy2
          exact hstrip y hy1 hy2)
    · by_cases hxm : x ∈ Dminus f
      · have hfd := humC.continuousOn_fderiv_of_isOpen hDmO (by norm_num)
        refine ((hfd x hxm).continuousAt (hDmO.mem_nhds hxm)).congr ?_ |>.continuousWithinAt
        filter_upwards [hDmO.mem_nhds hxm] with y hy
        simp [hy]
      · have hcw := hBCm.1.2.1 x (hstrip x hx
          (mem_of_mem_nhds (hnear x hx hxm) : x ∈ {y : R2 | hm < y 1}))
        have hcw' : ContinuousWithinAt Dum (closure (Dminus f)) x :=
          hcw.mono_of_mem_nhdsWithin (by
            filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hnear x hx hxm)]
              with y hy1 hy2
            exact hstrip y hy1 hy2)
        refine hcw'.congr_of_eventuallyEq ?_ (by simp [hxm])
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hnear x hx hxm)] with y hy1 hy2
        by_cases hym : y ∈ Dminus f
        · simp only [hym, if_true]
          exact (hBCm.1.2.2 y (hint y hym hy2)).fderiv
        · simp [hym]
    · have hxm := interior_closure_Dminus_i f hfc hx
      simp only [hxm, if_true]
      exact ((humC.differentiableOn (by norm_num) x hxm).differentiableAt
        (hDmO.mem_nhds hxm)).hasFDerivAt
  · have hgm : gpt f s ∉ Dminus f := by simp [Dminus, gpt, pt]
    simp only [hgm, if_false]
    set y : ℝ → R2 := fun t => gpt f s + t • e2i
    have hylim := tendsto_curve_i f s
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ∈ O ∩ Dplus f ∧ (y t) 1 < hp := by
      have hlt : f s < hp := lt_of_le_of_lt (hfs s) hhp
      have hO1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ∈ O :=
        hylim.eventually (hO.mem_nhds hsO)
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < hp - f s by linarith), hO1] with t ht hyO
      obtain ⟨c0, c1⟩ := curve_apply_i f s t
      refine ⟨⟨hyO, ?_⟩, ?_⟩
      · show f ((y t) 0) < (y t) 1
        simp only [y]; rw [c0, c1]; linarith [ht.1]
      · simp only [y]; rw [c1]; linarith [ht.2]
    have hDpO : IsOpen (Dplus f) := isOpen_lt (hfc.comp (by fun_prop)) (by fun_prop)
    have hstripP : ∀ (z : R2), z ∈ closure (Dplus f) → z 1 < hp → z ∈ stripPlus f hp :=
      fun z hz h => ⟨hz, fun h' => by simp only [Uplus, Set.mem_setOf_eq] at h'; linarith⟩
    have hgΓ : gpt f s ∈ stripPlus f hp := by
      refine hstripP _ ?_ (by simp [gpt, pt]; linarith [hfs s])
      exact mem_closure_of_tendsto hylim (hpos.mono fun t ht => ht.1.2)
    have hyS : Tendsto y (𝓝[>] 0) (𝓝[stripPlus f hp] (gpt f s)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hylim,
        hpos.mono fun t ht => hstripP _ (subset_closure ht.1.2) ht.2⟩
    have hylimO : Tendsto y (𝓝[>] 0) (𝓝 (gpt f s)) := hylim
    -- value
    have hval : up (gpt f s) = W (gpt f s) - ui (gpt f s) := by
      have l1 : Tendsto (fun t => up (y t)) (𝓝[>] 0) (𝓝 (up (gpt f s))) :=
        (hBCp.1.1 _ hgΓ).tendsto.comp hyS
      have cW := (hW.continuousOn.continuousAt (hO.mem_nhds hsO)).tendsto.comp hylimO
      have cu := (hui.continuousOn.continuousAt (hO.mem_nhds hsO)).tendsto.comp hylimO
      refine tendsto_nhds_unique l1 ((cW.sub cu).congr' ?_)
      filter_upwards [hpos] with t ht
      simp only [Function.comp_apply]
      rw [hag _ ht.1]; ring
    -- gradient
    have hgrad : Dup (gpt f s) = fderiv ℝ W (gpt f s) - fderiv ℝ ui (gpt f s) := by
      have hintP : ∀ (z : R2), z ∈ Dplus f → z 1 < hp → z ∈ interior (stripPlus f hp) := by
        intro z hz h
        have hO' : IsOpen (Dplus f ∩ {z : R2 | z 1 < hp}) :=
          hDpO.inter (isOpen_lt (by fun_prop) continuous_const)
        exact interior_maximal (fun w hw => hstripP w (subset_closure hw.1) hw.2) hO' ⟨hz, h⟩
      have l1 : Tendsto (fun t => Dup (y t)) (𝓝[>] 0) (𝓝 (Dup (gpt f s))) :=
        (hBCp.1.2.1 _ hgΓ).tendsto.comp hyS
      have hfW := hW.continuousOn_fderiv_of_isOpen hO le_rfl
      have hfu := hui.continuousOn_fderiv_of_isOpen hO le_rfl
      have cW := ((hfW _ hsO).continuousAt (hO.mem_nhds hsO)).tendsto.comp hylimO
      have cu := ((hfu _ hsO).continuousAt (hO.mem_nhds hsO)).tendsto.comp hylimO
      refine tendsto_nhds_unique l1 ((cW.sub cu).congr' ?_)
      filter_upwards [hpos] with t ht
      simp only [Function.comp_apply]
      have h1 := hBCp.1.2.2 _ (hintP _ ht.1.2 ht.2)
      have hOD : IsOpen (O ∩ Dplus f) := hO.inter hDpO
      have hev : up =ᶠ[𝓝 (y t)] fun x => W x - ui x := by
        filter_upwards [hOD.mem_nhds ht.1] with w hw
        rw [hag w hw]; ring
      have dW : DifferentiableAt ℝ W (y t) :=
        (hW.differentiableOn one_ne_zero _ ht.1.1).differentiableAt (hO.mem_nhds ht.1.1)
      have du : DifferentiableAt ℝ ui (y t) :=
        (hui.differentiableOn one_ne_zero _ ht.1.1).differentiableAt (hO.mem_nhds ht.1.1)
      rw [← h1.fderiv, hev.fderiv_eq]; exact (fderiv_sub dW du).symm
    refine ⟨?_, ?_⟩
    · have a := ht1 s
      simp only [incData] at a
      rw [hval] at a
      linear_combination -a
    · have a := ht2 s
      simp only [incData] at a
      rw [hgrad] at a
      simp only [ContinuousLinearMap.sub_apply] at a
      linear_combination -a


lemma normal_norm_i (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < arcDen f s := Real.sqrt_pos.mpr (by positivity)
  have hpt : ‖pt (deriv f s) (-1)‖ = arcDen f s := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [pt, arcDen]
    ring_nf
  rw [normal, norm_smul, hpt, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

lemma IsC1On.mono_i {S T : Set R2} {u : R2 → ℂ} {Du : R2 → (R2 →L[ℝ] ℂ)} (h : IsC1On S u Du)
    (hT : T ⊆ S) : IsC1On T u Du :=
  ⟨h.1.mono hT, h.2.1.mono hT, fun x hx => h.2.2 x (interior_mono hT hx)⟩

lemma l2_le_h1_i (D : Set R2) (w : R2 → ℂ) : l2Norm D w ≤ h1Norm D w := by
  unfold l2Norm h1Norm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num)
  rw [ENNReal.rpow_two]
  exact le_add_right (le_add_right le_rfl)

lemma h1Norm_mono_set_i {S T : Set R2} (hST : S ⊆ T) (w : R2 → ℂ) : h1Norm S w ≤ h1Norm T w := by
  unfold h1Norm
  exact ENNReal.rpow_le_rpow (lintegral_mono_set hST) (by norm_num)

lemma h1Norm_neg_i (D : Set R2) (w : R2 → ℂ) : h1Norm D (fun x => -w x) = h1Norm D w := by
  unfold h1Norm
  congr 1
  refine lintegral_congr fun x => ?_
  have : fderiv ℝ (fun x => -w x) x = -fderiv ℝ w x := fderiv_neg
  simp [this]

lemma h1Norm_add_le_i (D : Set R2) (hD : IsOpen D) (v w : R2 → ℂ)
    (hv : ContDiffOn ℝ 1 v D) (hw : ContDiffOn ℝ 1 w D) :
    h1Norm D (fun x => v x + w x) ≤ h1Norm D v + h1Norm D w := by
  have h := h1Norm_sub_le D hD v (fun x => -w x) hv hw.neg
  have e : (fun x => v x - -w x) = fun x => v x + w x := by funext x; ring
  rw [e, h1Norm_neg_i] at h
  exact h

lemma enorm_sq_le_i (z : ℂ) (C : ℝ) (h : ‖z‖ ≤ C) : ‖z‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)

lemma h1Norm_le_of_pointwise_i (D : Set R2) (hDm : MeasurableSet D) (hDv : volume D ≠ ⊤)
    (C : ℝ) : ∃ C' : ℝ, ∀ w : R2 → ℂ, (∀ x ∈ D, ‖w x‖ ≤ C ∧ ‖fderiv ℝ w x‖ ≤ C) →
      h1Norm D w ≤ ENNReal.ofReal C' := by
  refine ⟨(3 * C ^ 2 * (volume D).toReal) ^ (1 / 2 : ℝ), fun w hw => ?_⟩
  unfold h1Norm
  have hle : ∫⁻ x in D, ‖w x‖ₑ ^ 2 + ‖fderiv ℝ w x (EuclideanSpace.single 0 1)‖ₑ ^ 2 +
      ‖fderiv ℝ w x (EuclideanSpace.single 1 1)‖ₑ ^ 2 ≤
      ∫⁻ _ in D, ENNReal.ofReal (3 * C ^ 2) := by
    refine setLIntegral_mono' hDm fun x hx => ?_
    obtain ⟨h0, h1⟩ := hw x hx
    have hC : 0 ≤ C := (norm_nonneg _).trans h0
    have he : ∀ i : Fin 2, ‖fderiv ℝ w x (EuclideanSpace.single i 1)‖ ≤ C := fun i => by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      simp only [EuclideanSpace.norm_single, norm_one, mul_one]
      exact h1
    have e3 : ENNReal.ofReal (3 * C ^ 2) =
        ENNReal.ofReal (C ^ 2) + ENNReal.ofReal (C ^ 2) + ENNReal.ofReal (C ^ 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    rw [e3]
    exact add_le_add (add_le_add (enorm_sq_le_i _ _ h0) (enorm_sq_le_i _ _ (he 0)))
      (enorm_sq_le_i _ _ (he 1))
  refine (ENNReal.rpow_le_rpow hle (by norm_num)).trans ?_
  rw [setLIntegral_const, ← ENNReal.ofReal_toReal hDv, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal hDv, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]


lemma abs_coord_le_norm_j (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0


/-- Mirror of `cone_below_interface`: points in a cone around `-n` lie above `Γ`. -/
lemma cone_above_interface_j (f : ℝ → ℝ) (s0 : ℝ) (hf : DifferentiableAt ℝ f s0) :
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
  have h0 := abs_coord_le_norm_j v 0
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



lemma phi0_contDiffOn3 (z : R2) :
    ContDiffOn ℝ 3 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
  intro x hx
  have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ContDiffAt ℝ 3 (fun x' : R2 => ‖x' - z‖) x :=
    (contDiffAt_norm ℝ hx').comp x ((contDiffAt_id).sub contDiffAt_const)
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr hx'
  have hinv : ContDiffAt ℝ 3 (fun x' : R2 => 1 / ‖x' - z‖) x := by
    have := (contDiffAt_inv ℝ hpos.ne').comp x hn
    simpa [one_div, Function.comp_def] using this
  have hlog : ContDiffAt ℝ 3 (fun x' : R2 => Real.log (1 / ‖x' - z‖)) x :=
    (Real.contDiffAt_log.mpr (by positivity)).comp x hinv
  have hreal : ContDiffAt ℝ 3
      (fun x' : R2 => 1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖)) x :=
    contDiffAt_const.mul hlog
  have hc : ContDiffAt ℝ 3
      (fun x' : R2 => ((1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  simpa [Phi] using hc.contDiffWithinAt

lemma phi_contDiffOn3 (k : ℝ) (hk : 0 ≤ k) (z : R2) :
    ContDiffOn ℝ 3 (fun x => Phi k x z) {x | x ≠ z} := by
  have hs : ContDiff ℝ 3 (fun x : R2 => x - z) := contDiff_id.sub contDiff_const
  have haF : ContDiff ℝ 3 (aF k) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_PJ.comp (contDiff_tq k))
  have h1 : ContDiffOn ℝ 3 (fun x => aF k (x - z) * Phi 0 x z + bG k (x - z)) {x | x ≠ z} :=
    ((haF.comp hs).contDiffOn.mul (phi0_contDiffOn3 z)).add ((contDiff_bG k).comp hs).contDiffOn
  exact h1.congr fun x hx => phi_decomp' k hk x z hx

lemma dipole_contDiffOn2 (k : ℝ) (hk : 0 ≤ k) (z ν : R2) :
    ContDiffOn ℝ 2 (dipoleSource k z ν) {x | x ≠ z} := by
  have h := (phi_contDiffOn3 k hk z).fderiv_of_isOpen isOpen_ne (m := 2) (by norm_num)
  exact h.clm_apply contDiffOn_const

theorem solution (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1 ∧ lam1 ≤ 1) (hlam2 : 0 < lam2 ∧ lam2 ≤ 1)
    (hf1' : IsC2Lambda lam1 f1) (hf2' : IsC2Lambda lam2 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (hμ1 : μ1 = 1)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x)
    (s0 : ℝ) (hs : f2 s0 < f1 s0) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam1 D0 ∧
        Metric.ball (gpt f1 s0) (2 * δ) ∩ Dminus f1 ⊆ D0 ∧ D0 ⊆ Dminus f1 ∧
        ∀ u1 : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f1 kp k1 μ1
            (incData f1 (dipoleSource kp (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0) (normal f1 s0))).1
            (incData f1 (dipoleSource kp (gpt f1 s0 - (δ / (j : ℝ)) • normal f1 s0) (normal f1 s0))).2
            (u1 j).1 (u1 j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j → l2Norm D0 (u1 j).2 ≤ ENNReal.ofReal C := by
  classical
  set x0 : R2 := gpt f1 s0 with hx0def
  set n0 : R2 := normal f1 s0 with hn0def
  have hf1c : Continuous f1 := hf1.1.continuous
  have hf2c : Continuous f2 := hf2.1.continuous
  have hx0 : x0 ∈ Dplus f2 := by
    show f2 (x0 0) < x0 1
    simpa [x0, gpt, pt] using hs
  have hDp2O : IsOpen (Dplus f2) := isOpen_lt (hf2c.comp (by fun_prop)) (by fun_prop)
  obtain ⟨R0, hR0, hR0s⟩ := Metric.isOpen_iff.mp hDp2O x0 hx0
  have hkp : 0 < kp := hpar1.1
  have hk1 : 0 < k1 := hpar1.2.1
  have hkne : k1 ≠ kp := by
    intro h
    have := hpar1.2.2.2.2
    rw [hμ1, mul_one, h] at this
    exact this rfl
  obtain ⟨rc, hrc, hcone⟩ := cone_above_interface_j f1 s0 (hf1.1 s0)
  obtain ⟨r, hr, CU, hCU⟩ := dipole_scattered_local_bound f2 hf2 kp k2 μ2 hpar2 x0 hx0 n0
  obtain ⟨δa, hδa, hA⟩ := dipole_away_h1 f1 hf1 lam1 hlam1.1 hlam1.2 hf1' kp k1 μ1 hpar1 s0
  obtain ⟨δL, hδL, hL⟩ := itp_small_domain_l2_local f1 hf1 lam1 hlam1 hf1' s0 k1 kp hk1 hkp hkne
  refine ⟨min (min δa δL) (min (min (r / 4) (R0 / 4)) rc),
    lt_min (lt_min hδa hδL) (lt_min (lt_min (by linarith) (by linarith)) hrc),
    fun δ hδ hδ1 => ?_⟩
  simp only [lt_min_iff] at hδ1
  obtain ⟨⟨ha, hl⟩, ⟨hr4, hR4⟩, hrc'⟩ := hδ1
  obtain ⟨D0, hD0, hball, hsub, hsub3, CL, hCL⟩ := hL δ hδ hl
  refine ⟨D0, hD0, hball, hsub, fun u1 hu1 => ?_⟩
  obtain ⟨C1, hC1⟩ := hA δ hδ ha D0 hD0 hball hsub u1 hu1
  set xj : ℕ → R2 := fun j => x0 - (δ / (j : ℝ)) • n0 with hxjdef
  have hn1 : ‖n0‖ = 1 := normal_norm_i f1 s0
  have hn0 : n0 ≠ 0 := fun h => by rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  have hxjd : ∀ j : ℕ, 1 ≤ j → dist (xj j) x0 ≤ δ := by
    intro j hj
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    rw [dist_eq_norm]
    simp only [xj, sub_sub_cancel_left, norm_neg, norm_smul, hn1, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg hδ.le (by linarith : (0:ℝ) ≤ j))]
    exact div_le_self hδ.le hj'
  have hxj1 : ∀ j : ℕ, 1 ≤ j → xj j ∈ Dplus f1 := by
    intro j hj
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have ht : 0 < δ / (j : ℝ) := by positivity
    have hnv : ‖-((δ / (j : ℝ)) • n0)‖ = δ / j := by
      rw [norm_neg, norm_smul, hn1, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    have := hcone (-((δ / (j : ℝ)) • n0))
      (by rw [neg_ne_zero]; exact smul_ne_zero ht.ne' hn0)
      (by rw [hnv]; linarith [div_le_self hδ.le hj'])
      (by
        rw [hnv, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq, hn1]
        simp only [one_pow, mul_one, RCLike.conj_to_real]
        linarith)
    rw [← sub_eq_add_neg] at this
    exact this
  have hball4 : ball x0 (4 * δ) ⊆ Dplus f2 := fun x hx =>
    hR0s (ball_subset_ball (by linarith) hx)
  have hxj2 : ∀ j : ℕ, 1 ≤ j → xj j ∈ Dplus f2 := fun j hj =>
    hball4 (mem_ball.mpr (lt_of_le_of_lt (hxjd j hj) (by linarith)))
  have hDm : MeasurableSet D0 := hD0.1.measurableSet
  set A : Set R2 := D0 \ closedBall x0 (3 * δ / 2) with hAdef
  have hAo : IsOpen A := hD0.1.sdiff isClosed_closedBall
  have hAsub : A ⊆ D0 := Set.diff_subset
  have hAv : volume A ≠ ⊤ :=
    ((hD0.2.2.1.subset hAsub).measure_lt_top).ne
  obtain ⟨CP, hCP⟩ := h1Norm_le_of_pointwise_i A hAo.measurableSet hAv CU
  obtain ⟨Cd, hCd⟩ := dipole_away_bound kp hkp D0 hD0.1 hD0.2.2.1 x0 n0 δ hδ
  set T := max C1 0 + (max Cd 0 + max CP 0)
  refine ⟨max CL 0 * T, fun j hj => ?_⟩
  set yj := xj j with hyj
  have hyj1 : yj ∈ Dplus f1 := hxj1 j hj
  have hyj2 : yj ∈ Dplus f2 := hxj2 j hj
  have hyjr : yj ∈ ball x0 r := mem_ball.mpr (lt_of_le_of_lt (hxjd j hj) (by linarith))
  have hclD : closure D0 ⊆ {x : R2 | x 1 ≤ f1 (x 0)} :=
    (closure_mono hsub).trans (closure_Dminus_sub_i f1 hf1c)
  have hyjcl : yj ∉ closure D0 := fun h => by
    have h1 : yj 1 ≤ f1 (yj 0) := hclD h
    have h2 : f1 (yj 0) < yj 1 := hyj1
    linarith
  set O : Set R2 := ball x0 (4 * δ) ∩ {x | x ≠ yj} with hOdef
  have hOo : IsOpen O := isOpen_ball.inter isOpen_ne
  have hOp : O ⊆ Dplus f2 := fun x hx => hball4 hx.1
  have hD0O : D0 ⊆ O := fun x hx => ⟨ball_subset_ball (by linarith) (hsub3 hx),
    fun h => hyjcl (h ▸ subset_closure hx)⟩
  have hclO : closure D0 ∩ ball x0 (2 * δ) ⊆ O := fun x hx =>
    ⟨ball_subset_ball (by linarith) hx.2, fun h => hyjcl (h ▸ hx.1)⟩
  -- the dipole solution for the second scatterer
  obtain ⟨u2, hu2⟩ := dipole_tsp_exists f2 hf2 kp k2 μ2 hpar2 yj hyj2 n0
  have hag2 := dipole_upper_agree_cross f1 f2 hf1 hf2 kp k1 k2 μ1 μ2 hpar1 hpar2 U1 U2 hU1 hU2
    hagree yj ⟨hyj1, hyj2⟩ n0 (u1 j) u2 (hu1 j hj) hu2
  have hu2c := hu2
  obtain ⟨-, -, -, -, -, -, hupC, -, -, -, hHp, -⟩ := hu2
  obtain ⟨-, -, -, -, -, -, -, humC, -, -, -, hHm, -⟩ := hu1 j hj
  have hΦ2 : ContDiffOn ℝ 2 (dipoleSource kp yj n0) {x | x ≠ yj} :=
    dipole_contDiffOn2 kp hkp.le yj n0
  set W : R2 → ℂ := fun x => dipoleSource kp yj n0 x + u2.1 x with hWdef
  have hW2 : ContDiffOn ℝ 2 W O := (hΦ2.mono Set.inter_subset_right).add (hupC.mono hOp)
  have hWD : ContDiffOn ℝ 2 W D0 := hW2.mono hD0O
  have hVD : ContDiffOn ℝ 2 (u1 j).2 D0 := humC.mono hsub
  have hHW : IsHelmholtzOn D0 kp W := by
    intro x hx
    have hxO := hD0O hx
    have c1 : ContDiffAt ℝ 2 (dipoleSource kp yj n0) x :=
      (hΦ2 x hxO.2).contDiffAt (isOpen_ne.mem_nhds hxO.2)
    have c2 : ContDiffAt ℝ 2 u2.1 x :=
      (hupC x (hOp hxO)).contDiffAt (hDp2O.mem_nhds (hOp hxO))
    have hadd := c1.laplacian_add c2
    simp only [Pi.add_def] at hadd
    show Laplacian.laplacian (fun x => dipoleSource kp yj n0 x + u2.1 x) x +
      (kp : ℂ) ^ 2 * (dipoleSource kp yj n0 x + u2.1 x) = 0
    rw [hadd]
    have e1 := dipole_helmholtz kp hkp.le yj n0 x hxO.2
    have e2 := hHp x (hOp hxO)
    linear_combination e1 + e2
  have hui1 : ContDiffOn ℝ 1 (dipoleSource kp yj n0) O :=
    (hΦ2.mono Set.inter_subset_right).of_le (by norm_num)
  have hW1 : ContDiffOn ℝ 1 W O := hW2.of_le (by norm_num)
  obtain ⟨DV, hDV, hbdV⟩ := cross_upper f1 hf1 kp k1 μ1 (dipoleSource kp yj n0) (u1 j).1 (u1 j).2
    (hu1 j hj) O hOo W hui1 hW1 (fun x hx => by
      show dipoleSource kp yj n0 x + u2.1 x = dipoleSource kp yj n0 x + (u1 j).1 x
      rw [hag2 x ⟨hx.2, hOp hx.1⟩])
  have hWC1 : IsC1On (closure D0 ∩ ball x0 (2 * δ)) W (fderiv ℝ W) := by
    refine ⟨hW1.continuousOn.mono hclO,
      (hW1.continuousOn_fderiv_of_isOpen hOo le_rfl).mono hclO, fun x hx => ?_⟩
    have hxO := hclO (interior_subset hx)
    exact ((hW1.differentiableOn one_ne_zero x hxO).differentiableAt
      (hOo.mem_nhds hxO)).hasFDerivAt
  have hcl : closure D0 ∩ ball x0 (2 * δ) ⊆ closure (Dminus f1) :=
    fun x hx => closure_mono hsub hx.1
  have hitp := hCL (u1 j).2 W DV (fderiv ℝ W) hVD hWD (fun x hx => hHm x (hsub hx)) hHW
    (IsC1On.mono_i hDV hcl) hWC1 (fun s hs' => by
      have hsO : gpt f1 s ∈ O := by
        refine ⟨ball_subset_ball (by linarith) hs', fun h => ?_⟩
        have := hyj1
        rw [← h] at this
        simp [Dplus, gpt, pt] at this
      obtain ⟨b1, b2⟩ := hbdV s hsO
      refine ⟨b1, ?_⟩
      rw [← b2, hμ1]
      simp)
  -- bounds away from the source
  have hpt : ∀ x ∈ A, ‖u2.1 x‖ ≤ CU ∧ ‖fderiv ℝ u2.1 x‖ ≤ CU := fun x hx =>
    hCU yj hyjr u2 hu2c x (ball_subset_ball (by linarith) (hsub3 (hAsub hx)))
  have hU2b : h1Norm A u2.1 ≤ ENNReal.ofReal CP := hCP _ hpt
  have hdb : h1Norm A (dipoleSource kp yj n0) ≤ ENNReal.ofReal Cd :=
    hCd yj (mem_closedBall.mpr (hxjd j hj))
  have hWa : h1Norm A W ≤ ENNReal.ofReal (max Cd 0 + max CP 0) := by
    refine (h1Norm_add_le_i A hAo _ _ (hui1.mono (hAsub.trans hD0O))
      ((hupC.of_le (by norm_num)).mono (hAsub.trans (hD0O.trans hOp)))).trans ?_
    rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    exact add_le_add (hdb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      (hU2b.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hVa : h1Norm A (u1 j).2 ≤ ENNReal.ofReal (max C1 0) :=
    (hC1 j hj).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  calc l2Norm D0 (u1 j).2 ≤ l2Norm D0 (u1 j).2 + l2Norm D0 W := le_self_add
    _ ≤ _ := hitp
    _ ≤ ENNReal.ofReal (max CL 0) * (ENNReal.ofReal (max C1 0) +
          ENNReal.ofReal (max Cd 0 + max CP 0)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) (add_le_add hVa hWa)
    _ = ENNReal.ofReal (max CL 0 * T) := by
        rw [← ENNReal.ofReal_add (le_max_right _ _) (by positivity),
          ← ENNReal.ofReal_mul (le_max_right _ _)]
