-- Prove2me | solution 1 for RoughSurfaceScattering.helmholtz_h1_blowup
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:58:26.91941+00:00
-- url     : https://prove2.me/submissions/d0d4f91d-e896-4de5-a320-e0fa40feec08

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_dipole_l2_blowup
import Theorems.Thm_RoughSurfaceScattering_laplace_l2_bound

open MeasureTheory
open RoughSurfaceScattering

/-- A real power series with infinite radius of convergence is `C¹`. -/
lemma contDiff_powerSeries (c : ℕ → ℝ)
    (hc : ∀ r : ℝ, 0 ≤ r → Summable fun n => |c n| * r ^ n) :
    ContDiff ℝ 1 (fun t : ℝ => ∑' n, c n * t ^ n) := by
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

lemma contDiff_PJ : ContDiff ℝ 1 PJ := by
  refine contDiff_powerSeries cJ fun r hr => ?_
  refine (Real.summable_pow_div_factorial r).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [cJ, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity),
    div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_left (by positivity) hf (fact_sq_ge n)

lemma contDiff_PS : ContDiff ℝ 1 PS := by
  refine contDiff_powerSeries cS fun r hr => ?_
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

lemma contDiff_tq (k : ℝ) : ContDiff ℝ 1 (tq k) := by
  have : tq k = fun y : R2 => (k ^ 2 / 4) * ‖y‖ ^ 2 := by
    funext y; unfold tq; ring
  rw [this]
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

lemma contDiff_aF (k : ℝ) : ContDiff ℝ 1 (aF k) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_PJ.comp (contDiff_tq k))

lemma contDiff_bF (k : ℝ) : ContDiff ℝ 1 (bF k) := by
  have h1 : ContDiff ℝ 1 (fun y : R2 => (PJ (tq k y) : ℂ)) := contDiff_aF k
  have h2 : ContDiff ℝ 1 (fun y : R2 =>
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

lemma phi0_contDiffOn (z : R2) :
    ContDiffOn ℝ 1 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
  intro x hx
  have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ContDiffAt ℝ 1 (fun x' : R2 => ‖x' - z‖) x :=
    (contDiffAt_norm ℝ hx').comp x ((contDiffAt_id).sub contDiffAt_const)
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr hx'
  have hinv : ContDiffAt ℝ 1 (fun x' : R2 => 1 / ‖x' - z‖) x := by
    have := (contDiffAt_inv ℝ hpos.ne').comp x hn
    simpa [one_div, Function.comp_def] using this
  have hlog : ContDiffAt ℝ 1 (fun x' : R2 => Real.log (1 / ‖x' - z‖)) x :=
    (Real.contDiffAt_log.mpr (by positivity)).comp x hinv
  have hreal : ContDiffAt ℝ 1
      (fun x' : R2 => 1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖)) x :=
    contDiffAt_const.mul hlog
  have hc : ContDiffAt ℝ 1
      (fun x' : R2 => ((1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  simpa [Phi] using hc.contDiffWithinAt

lemma phi_contDiffOn' (k : ℝ) (hk : 0 < k) (z : R2) :
    ContDiffOn ℝ 1 (fun x => Phi k x z) {x | x ≠ z} := by
  have hs : ContDiff ℝ 1 (fun x : R2 => x - z) := contDiff_id.sub contDiff_const
  have h1 : ContDiffOn ℝ 1 (fun x => aF k (x - z) * Phi 0 x z + bF k (x - z)) {x | x ≠ z} :=
    (((contDiff_aF k).comp hs).contDiffOn.mul (phi0_contDiffOn z)).add
      ((contDiff_bF k).comp hs).contDiffOn
  exact h1.congr fun x hx => phi_decomp k hk x z hx

/-- `∂_ν Φ_k = a ∂_ν Φ₀ + Φ₀ ∂_ν a + ∂_ν b` away from the source point. -/
lemma fderiv_phi_apply (k : ℝ) (hk : 0 < k) (z ν x : R2) (hx : x ≠ z) :
    fderiv ℝ (fun x => Phi k x z) x ν =
      aF k (x - z) * dipoleSource 0 z ν x + Phi 0 x z * fderiv ℝ (aF k) (x - z) ν +
        fderiv ℝ (bF k) (x - z) ν := by
  have hev : (fun x => Phi k x z) =ᶠ[nhds x]
      (fun x => aF k (x - z) * Phi 0 x z + bF k (x - z)) :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hx) fun y hy => phi_decomp k hk y z hy
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const z
  have ha : HasFDerivAt (fun x => aF k (x - z))
      ((fderiv ℝ (aF k) (x - z)).comp (ContinuousLinearMap.id ℝ R2)) x := by
    have := (((contDiff_aF k).differentiable one_ne_zero) (x - z)).hasFDerivAt.comp x hsub
    simpa [Function.comp_def] using this
  have hb : HasFDerivAt (fun x => bF k (x - z))
      ((fderiv ℝ (bF k) (x - z)).comp (ContinuousLinearMap.id ℝ R2)) x := by
    have := (((contDiff_bF k).differentiable one_ne_zero) (x - z)).hasFDerivAt.comp x hsub
    simpa [Function.comp_def] using this
  have hp : HasFDerivAt (fun x => Phi 0 x z) (fderiv ℝ (fun x' => Phi 0 x' z) x) x :=
    (((phi0_contDiffOn z).contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt
      one_ne_zero).hasFDerivAt
  have htot : HasFDerivAt (fun x => aF k (x - z) * Phi 0 x z + bF k (x - z)) _ x :=
    (ha.mul hp).add hb
  rw [hev.fderiv_eq, htot.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul, dipoleSource]

/-- `|L ν|² ≤ |L e₁|² + |L e₂|²` for a unit vector `ν`. -/
lemma clm_unit_sq_le (L : R2 →L[ℝ] ℂ) (ν : R2) (hν : ‖ν‖ = 1) :
    ‖L ν‖ ^ 2 ≤ ‖L (EuclideanSpace.single 0 1)‖ ^ 2 + ‖L (EuclideanSpace.single 1 1)‖ ^ 2 := by
  have hdec : ν = ν 0 • EuclideanSpace.single 0 (1 : ℝ) + ν 1 • EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp
  have hsum : ν 0 ^ 2 + ν 1 ^ 2 = 1 := by
    have := EuclideanSpace.norm_sq_eq ν
    rw [hν, Fin.sum_univ_two] at this
    simpa [Real.norm_eq_abs, sq_abs] using this.symm
  set a := ‖L (EuclideanSpace.single 0 1)‖
  set b := ‖L (EuclideanSpace.single 1 1)‖
  have hle : ‖L ν‖ ≤ |ν 0| * a + |ν 1| * b := by
    calc ‖L ν‖ = ‖ν 0 • L (EuclideanSpace.single 0 1) + ν 1 • L (EuclideanSpace.single 1 1)‖ := by
          conv_lhs => rw [hdec]
          rw [map_add, map_smul, map_smul]
      _ ≤ _ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have h0 : 0 ≤ ‖L ν‖ := norm_nonneg _
  have habs : |ν 0| ^ 2 + |ν 1| ^ 2 = 1 := by rw [sq_abs, sq_abs]; exact hsum
  nlinarith [sq_nonneg (|ν 0| * b - |ν 1| * a), abs_nonneg (ν 0), abs_nonneg (ν 1)]

lemma normal_norm (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < 1 + deriv f s ^ 2 := by positivity
  have hpt : ‖pt (deriv f s) (-1)‖ = Real.sqrt (1 + deriv f s ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [pt, Fin.sum_univ_two]
    ring_nf
  rw [normal, norm_smul, hpt, arcDen, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'

/-- Near the origin `|a| ≥ 1/2` and the derivatives of `a`, `b` are bounded. -/
lemma local_bounds (k : ℝ) : ∃ ρ0 > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∀ y : R2, ‖y‖ ≤ ρ0 →
    1 / 2 ≤ ‖aF k y‖ ∧ ‖fderiv ℝ (aF k) y‖ ≤ M ∧ ‖fderiv ℝ (bF k) y‖ ≤ M := by
  have hcont := (contDiff_aF k).continuous.continuousAt (x := (0 : R2))
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ε, hε, hball⟩ := hcont (1 / 2) (by norm_num)
  set ρ0 := ε / 2
  have hfa := (contDiff_aF k).continuous_fderiv one_ne_zero
  have hfb := (contDiff_bF k).continuous_fderiv one_ne_zero
  obtain ⟨Ma, hMa⟩ := (isCompact_closedBall (0 : R2) ρ0).exists_bound_of_continuousOn
    hfa.continuousOn
  obtain ⟨Mb, hMb⟩ := (isCompact_closedBall (0 : R2) ρ0).exists_bound_of_continuousOn
    hfb.continuousOn
  refine ⟨ρ0, by positivity, max (max Ma Mb) 0, le_max_right _ _, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · have hy' : dist y 0 < ε := by
      rw [dist_zero_right]
      have h := hy
      simp only [ρ0] at h
      linarith
    have := hball hy'
    rw [aF_zero, dist_eq_norm] at this
    have h2 := norm_sub_norm_le (1 : ℂ) (aF k y)
    rw [norm_one, norm_sub_rev] at h2
    linarith
  · exact (hMa y (by simpa using hy)).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hMb y (by simpa using hy)).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (s0 δ : ℝ) (hδ : 0 < δ)
    (D0 : Set R2) (hD0 : Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0)
    (k : ℝ) (hk : 0 < k) :
    ∀ C : ℝ, ∃ j : ℕ, 1 ≤ j ∧ ENNReal.ofReal C <
      h1Norm D0 (fun x => Phi k x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) := by
  intro C
  set x0 := gpt f s0
  set n := normal f s0
  have hn1 : ‖n‖ = 1 := normal_norm f s0
  obtain ⟨ρ0, hρ0, M, hM0, hloc⟩ := local_bounds k
  -- a small sub-domain where the local bounds hold
  set m : ℕ := ⌈3 * δ / ρ0⌉₊ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm3 : 3 * (δ / m) ≤ ρ0 := by
    have h1 : 3 * δ / ρ0 ≤ m := by
      have := Nat.le_ceil (3 * δ / ρ0)
      have h2 : ((⌈3 * δ / ρ0⌉₊ : ℕ) : ℝ) ≤ m := by rw [hm]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hρ0] at h1
    rw [← mul_div_assoc, div_le_iff₀ hmpos]
    linarith
  set δ' := δ / m with hδ'
  have hδ'pos : 0 < δ' := by positivity
  have hδ'le : δ' ≤ δ := div_le_self hδ.le (by exact_mod_cast hm1)
  set D1 := Metric.ball x0 (2 * δ') ∩ Dminus f with hD1
  have hD1sub : D1 ⊆ D0 := fun x hx =>
    hD0 ⟨Metric.ball_subset_ball (by linarith) hx.1, hx.2⟩
  have hD1m : MeasurableSet D1 := by
    refine measurableSet_ball.inter ?_
    exact measurableSet_lt (by fun_prop) (hf.1.continuous.measurable.comp (by fun_prop))
  have hD1b : Bornology.IsBounded D1 := Metric.isBounded_ball.subset Set.inter_subset_left
  have hD1fin : volume D1 ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_left)
  obtain ⟨C4, hC4⟩ := laplace_l2_bound f s0 δ' D1 hD1b M
  set K3 := eLpNorm (fun _ : R2 => M) 2 (volume.restrict D1) with hK3
  have hK3fin : K3 ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (eLpNorm_le_of_ae_bound (μ := volume.restrict D1)
      (p := 2) (f := fun _ : R2 => M) (C := M) (ae_of_all _ fun _ => by
        rw [Real.norm_of_nonneg hM0]))
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_)
      ENNReal.ofReal_ne_top
    rwa [Measure.restrict_apply_univ]
  set X : ENNReal := 2 * (ENNReal.ofReal C + ENNReal.ofReal C4 + K3) with hX
  have hXfin : X ≠ ⊤ := by
    rw [hX]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
        ENNReal.ofReal_ne_top⟩, hK3fin⟩)
  obtain ⟨j', hj', hblow⟩ := dipole_l2_blowup f hf s0 δ' hδ'pos D1 subset_rfl X.toReal
  rw [ENNReal.ofReal_toReal hXfin] at hblow
  refine ⟨m * j', Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  have hj'pos : (0 : ℝ) < j' := by exact_mod_cast hj'
  have hz : δ / ((m * j' : ℕ) : ℝ) = δ' / (j' : ℝ) := by
    rw [hδ']; push_cast; field_simp
  rw [hz]
  set z := x0 - (δ' / (j' : ℝ)) • n with hzdef
  by_contra hcon
  push Not at hcon
  set u := fun x => Phi k x z
  set w : R2 → ℂ := fun x => fderiv ℝ u x n
  -- `‖∂ₙu‖_{L²(D₁)} ≤ ‖u‖_{H¹(D₀)}`
  have hw : eLpNorm w 2 (volume.restrict D1) ≤ h1Norm D0 u := by
    have h1 : eLpNorm w 2 (volume.restrict D1) ≤ h1Norm D1 u := by
      unfold h1Norm
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat]
      refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num)
      have key := clm_unit_sq_le (fderiv ℝ u x) n hn1
      rw [ENNReal.rpow_two]
      simp only [w, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : 0 ≤ ‖u x‖ ^ 2 := by positivity
      linarith
    refine h1.trans ?_
    unfold h1Norm
    exact ENNReal.rpow_le_rpow (lintegral_mono_set hD1sub) (by norm_num)
  -- the pointwise bound for the Laplace dipole
  have hae : ∀ᵐ x ∂(volume.restrict D1), x ≠ z := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (measure_singleton z).le)
  have hpt : ∀ᵐ x ∂(volume.restrict D1), ‖dipoleSource 0 z n x‖ ≤
      2 * (‖w x‖ + M * ‖Phi 0 x z‖ + M) := by
    filter_upwards [hae, ae_restrict_mem hD1m] with x hx hxD
    have hxz : ‖x - z‖ ≤ ρ0 := by
      have h1 : ‖x - x0‖ < 2 * δ' := by
        have := hxD.1; rwa [Metric.mem_ball, dist_eq_norm] at this
      have h2 : ‖x0 - z‖ ≤ δ' := by
        rw [hzdef, sub_sub_cancel, norm_smul, hn1, mul_one, Real.norm_of_nonneg (by positivity)]
        exact div_le_self hδ'pos.le (by exact_mod_cast hj')
      calc ‖x - z‖ = ‖(x - x0) + (x0 - z)‖ := by congr 1; abel
        _ ≤ ‖x - x0‖ + ‖x0 - z‖ := norm_add_le _ _
        _ ≤ 3 * δ' := by linarith
        _ ≤ ρ0 := hm3
    obtain ⟨hA, hDa, hDb⟩ := hloc (x - z) hxz
    have hform := fderiv_phi_apply k hk z n x hx
    have hDa' : ‖fderiv ℝ (aF k) (x - z) n‖ ≤ M := by
      calc _ ≤ ‖fderiv ℝ (aF k) (x - z)‖ * ‖n‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M := by rw [hn1, mul_one]; exact hDa
    have hDb' : ‖fderiv ℝ (bF k) (x - z) n‖ ≤ M := by
      calc _ ≤ ‖fderiv ℝ (bF k) (x - z)‖ * ‖n‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M := by rw [hn1, mul_one]; exact hDb
    have hAd : aF k (x - z) * dipoleSource 0 z n x =
        w x - Phi 0 x z * fderiv ℝ (aF k) (x - z) n - fderiv ℝ (bF k) (x - z) n := by
      simp only [w, u, hform]; ring
    have hnorm : ‖aF k (x - z)‖ * ‖dipoleSource 0 z n x‖ ≤ ‖w x‖ + M * ‖Phi 0 x z‖ + M := by
      rw [← norm_mul, hAd]
      calc _ ≤ ‖w x - Phi 0 x z * fderiv ℝ (aF k) (x - z) n‖ + ‖fderiv ℝ (bF k) (x - z) n‖ :=
            norm_sub_le _ _
        _ ≤ ‖w x‖ + ‖Phi 0 x z * fderiv ℝ (aF k) (x - z) n‖ + ‖fderiv ℝ (bF k) (x - z) n‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ ‖w x‖ + M * ‖Phi 0 x z‖ + M := by
            rw [norm_mul]
            have := mul_le_mul_of_nonneg_left hDa' (norm_nonneg (Phi 0 x z))
            linarith
    have hd0 := norm_nonneg (dipoleSource 0 z n x)
    nlinarith
  -- measurability of the comparison function
  have hwm : AEStronglyMeasurable (fun x => ‖w x‖) (volume.restrict D1) :=
    (measurable_fderiv_apply_const ℝ u n).norm.aestronglyMeasurable
  have hphim : AEStronglyMeasurable (fun x => M * ‖Phi 0 x z‖) (volume.restrict D1) := by
    have : Measurable fun x => Phi 0 x z := by
      simp only [Phi, if_true]; fun_prop
    exact (this.norm.const_mul M).aestronglyMeasurable
  have hbound : eLpNorm (dipoleSource 0 z n) 2 (volume.restrict D1) ≤ X := by
    calc eLpNorm (dipoleSource 0 z n) 2 (volume.restrict D1)
        ≤ eLpNorm (fun x => 2 * (‖w x‖ + M * ‖Phi 0 x z‖ + M)) 2 (volume.restrict D1) :=
          eLpNorm_mono_ae_real hpt
      _ = 2 * eLpNorm (fun x => ‖w x‖ + M * ‖Phi 0 x z‖ + M) 2 (volume.restrict D1) := by
          have : (fun x => 2 * (‖w x‖ + M * ‖Phi 0 x z‖ + M)) =
              (2 : ℝ) • (fun x => ‖w x‖ + M * ‖Phi 0 x z‖ + M) := by
            funext x; simp [smul_eq_mul]
          rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num)]
          norm_num
      _ ≤ 2 * (eLpNorm (fun x => ‖w x‖) 2 (volume.restrict D1) +
            eLpNorm (fun x => M * ‖Phi 0 x z‖) 2 (volume.restrict D1) + K3) := by
          gcongr
          refine (eLpNorm_add_le (hwm.add hphim) aestronglyMeasurable_const (by norm_num)).trans ?_
          gcongr
          exact eLpNorm_add_le hwm hphim (by norm_num)
      _ ≤ X := by
          rw [hX]
          gcongr
          · rw [eLpNorm_norm]
            exact hw.trans hcon
          · have h4 := hC4 j' hj'
            unfold l2Norm at h4
            refine le_of_eq_of_le (eLpNorm_congr_norm_ae (ae_of_all _ fun x => ?_)) h4
            simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
            left; rfl
  exact absurd (hblow.trans_le (by unfold l2Norm; exact hbound)) (lt_irrefl _)
