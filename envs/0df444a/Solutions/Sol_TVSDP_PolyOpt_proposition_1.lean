-- Prove2me | solution 1 for TVSDP.PolyOpt.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:33:17.619522+00:00
-- url     : https://prove2.me/submissions/328e6404-c4c8-4bf1-993b-1f7d931b5740

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Mollifier

set_option autoImplicit false
open MeasureTheory Set Filter Topology TVSDP.PolyOpt

lemma mol_J_eq (t : ℝ) : J t = cJ * expNegInvGlue (1 - t ^ 2) := by
  unfold J
  by_cases h : |t| < 1
  · rw [if_pos h]
    have hp : 0 < 1 - t ^ 2 := by
      have := sq_lt_one_iff_abs_lt_one t |>.mpr h
      linarith
    unfold expNegInvGlue
    rw [if_neg (not_le.mpr hp)]
    congr 2
    rw [neg_div, one_div]
  · rw [if_neg h]
    have : 1 - t ^ 2 ≤ 0 := by
      have := one_le_sq_iff_one_le_abs t |>.mpr (not_lt.mp h)
      linarith
    rw [expNegInvGlue.zero_of_nonpos this, mul_zero]

lemma mol_cJ_nonneg : 0 ≤ cJ := by
  unfold cJ
  apply inv_nonneg.mpr
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t _
  exact (Real.exp_pos _).le

lemma mol_glue_le_one (x : ℝ) : expNegInvGlue x ≤ 1 := by
  unfold expNegInvGlue
  split_ifs with h
  · exact zero_le_one
  · rw [Real.exp_le_one_iff]
    have : 0 < x := not_le.mp h
    have := inv_pos.mpr this
    linarith

lemma mol_J_nonneg (t : ℝ) : 0 ≤ J t := by
  rw [mol_J_eq]; exact mul_nonneg mol_cJ_nonneg (expNegInvGlue.nonneg _)

lemma mol_J_le (t : ℝ) : J t ≤ cJ := by
  rw [mol_J_eq]
  calc cJ * expNegInvGlue (1 - t ^ 2) ≤ cJ * 1 :=
        mul_le_mul_of_nonneg_left (mol_glue_le_one _) mol_cJ_nonneg
    _ = cJ := mul_one _

lemma mol_J_zero (t : ℝ) (h : 1 ≤ |t|) : J t = 0 := by
  unfold J; rw [if_neg (not_lt.mpr h)]

lemma mol_J_cont : Continuous J := by
  have : J = fun t => cJ * expNegInvGlue (1 - t ^ 2) := funext mol_J_eq
  rw [this]
  exact continuous_const.mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2))

lemma mol_J_integrable : Integrable J := by
  apply Continuous.integrable_of_hasCompactSupport mol_J_cont
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  intro x hx
  apply mol_J_zero
  by_contra h
  apply hx
  rw [not_le, abs_lt] at h
  exact ⟨h.1.le, h.2.le⟩

lemma mol_Jint_le_one : ∫ t, J t ≤ 1 := by
  have h1 : ∫ t, J t = ∫ t in Ioc (-1:ℝ) 1, J t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply mol_J_zero
    by_contra h
    apply hx
    rw [not_le, abs_lt] at h
    exact ⟨h.1, h.2.le⟩
  have h2 : ∫ t in Ioc (-1:ℝ) 1, J t = cJ * ∫ t in (-1:ℝ)..1, Real.exp (-1 / (1 - t ^ 2)) := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_const_mul]
    rw [setIntegral_congr_set (Ioo_ae_eq_Ioc).symm]
    rw [setIntegral_congr_set (Ioo_ae_eq_Ioc).symm]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    simp only [J]
    rw [if_pos (abs_lt.mpr hx)]
  rw [h1, h2]
  unfold cJ
  by_cases h0 : (∫ t in (-1:ℝ)..1, Real.exp (-1 / (1 - t ^ 2))) = 0
  · rw [h0]; simp
  · rw [inv_mul_cancel₀ h0]

lemma mol_Jint_interval (a b : ℝ) (hab : a ≤ b) : ∫ t in a..b, J t ≤ 1 := by
  rw [intervalIntegral.integral_of_le hab]
  calc ∫ t in Ioc a b, J t ≤ ∫ t, J t :=
        setIntegral_le_integral mol_J_integrable (Eventually.of_forall mol_J_nonneg)
    _ ≤ 1 := mol_Jint_le_one

lemma mol_phi_int (v : ℕ) (hv : 1 ≤ v) (t : ℝ) :
    ∫ s in (0:ℝ)..1, (v : ℝ) * J (v * (t - s)) ≤ 1 := by
  have hv0 : (v : ℝ) ≠ 0 := by positivity
  have hvpos : (0:ℝ) < v := by positivity
  rw [intervalIntegral.integral_const_mul]
  have : ∫ s in (0:ℝ)..1, J (v * (t - s)) = ∫ s in (0:ℝ)..1, J (v * t - v * s) := by
    congr 1; ext s; rw [mul_sub]
  rw [this, intervalIntegral.integral_comp_sub_mul (fun u => J u) hv0 ((v:ℝ) * t)]
  simp only [smul_eq_mul]
  have h := mol_Jint_interval ((v:ℝ) * t - v * 1) (v * t - v * 0) (by nlinarith)
  calc (v:ℝ) * ((v:ℝ)⁻¹ * ∫ u in ((v:ℝ) * t - v * 1)..(v * t - v * 0), J u)
      = ∫ u in ((v:ℝ) * t - v * 1)..(v * t - v * 0), J u := by field_simp
    _ ≤ 1 := h

lemma mol_intOn (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ s ∈ Icc (0:ℝ) 1, |g s| ≤ C) :
    IntervalIntegrable g volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  apply Measure.integrableOn_of_bounded (M := C) (by simp)
  · exact hg.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall (fun s hs => by
      rw [Real.norm_eq_abs]; exact hb s ⟨hs.1.le, hs.2⟩)

lemma mol_phi_meas (v : ℕ) (t : ℝ) : Measurable (fun s : ℝ => (v : ℝ) * J (v * (t - s))) :=
  (measurable_const.mul (mol_J_cont.measurable.comp (measurable_const.mul (measurable_const.sub measurable_id))))

lemma mol_rate (a : Polynomial ℝ) (x : ℝ → ℝ) (hx : Measurable x) (L γ : ℝ)
    (hL : ∀ t ∈ Icc (0:ℝ) 1, |a.derivative.eval t| ≤ L)
    (hγ : ∀ t ∈ Icc (0:ℝ) 1, |x t| ≤ γ) (v : ℕ) (hv : 1 ≤ v) :
    ∀ t ∈ Icc (0:ℝ) 1,
      |a.eval t * Mv v x t - Mv v (fun s => a.eval s * x s) t| ≤ L * γ / v := by
  intro t ht
  have hvpos : (0:ℝ) < v := by positivity
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL 0 ⟨le_refl _, zero_le_one⟩)
  have hγ0 : 0 ≤ γ := le_trans (abs_nonneg _) (hγ 0 ⟨le_refl _, zero_le_one⟩)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, ∀ s, φ s = (v : ℝ) * J (v * (t - s)) := ⟨_, fun _ => rfl⟩
  have hφ0 : ∀ s, 0 ≤ φ s := fun s => by rw [hφ]; exact mul_nonneg hvpos.le (mol_J_nonneg _)
  have hφb : ∀ s, φ s ≤ v * cJ := fun s => by
    rw [hφ]; exact mul_le_mul_of_nonneg_left (mol_J_le _) hvpos.le
  have hφm : Measurable φ := by
    have : φ = fun s => (v : ℝ) * J (v * (t - s)) := funext hφ
    rw [this]; exact mol_phi_meas v t
  have hi1 : IntervalIntegrable (fun s => φ s * x s) volume 0 1 :=
    mol_intOn _ (hφm.mul hx) (v * cJ * γ) (fun s hs => by
      rw [abs_mul, abs_of_nonneg (hφ0 s)]
      exact mul_le_mul (hφb s) (hγ s hs) (abs_nonneg _) (by positivity [mol_cJ_nonneg]))
  have hi2 : IntervalIntegrable (fun s => φ s * (a.eval s * x s)) volume 0 1 := by
    obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
      (a.continuous.continuousOn)
    refine mol_intOn _ (hφm.mul ((a.continuous.measurable).mul hx)) (v * cJ * (A * γ)) (fun s hs => ?_)
    rw [abs_mul, abs_of_nonneg (hφ0 s), abs_mul]
    refine mul_le_mul (hφb s) (mul_le_mul ?_ (hγ s hs) (abs_nonneg _) ?_) (by positivity) (by positivity [mol_cJ_nonneg])
    · have := hA s hs; simpa using this
    · exact le_trans (abs_nonneg _) (by simpa using hA 0 ⟨le_refl _, zero_le_one⟩)
  have hdiff : a.eval t * Mv v x t - Mv v (fun s => a.eval s * x s) t
      = ∫ s in (0:ℝ)..1, φ s * ((a.eval t - a.eval s) * x s) := by
    unfold Mv
    simp_rw [← hφ]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hi1.const_mul (a.eval t)) hi2]
    congr 1; ext s
    ring
  rw [hdiff]
  have hbound : ∀ s ∈ Ioc (0:ℝ) 1, ‖φ s * ((a.eval t - a.eval s) * x s)‖ ≤ (L * γ / v) * φ s := by
    intro s hs
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hφ0 s)]
    by_cases hlt : |(v:ℝ) * (t - s)| < 1
    · have hts : |t - s| ≤ 1 / v := by
        rw [abs_mul, abs_of_pos hvpos] at hlt
        rw [le_div_iff₀ hvpos]; nlinarith
      have hmvt : |a.eval t - a.eval s| ≤ L * |t - s| := by
        have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u => a.eval u) (s := Icc (0:ℝ) 1)
          (C := L) (fun u _ => a.differentiableAt) (fun u hu => by
            rw [Polynomial.deriv, Real.norm_eq_abs]; exact hL u hu) (convex_Icc 0 1) hs' ht
        simpa using this
      have h1 : |a.eval t - a.eval s| ≤ L / v := by
        refine hmvt.trans ?_
        calc L * |t - s| ≤ L * (1 / v) := mul_le_mul_of_nonneg_left hts hL0
          _ = L / v := by ring
      have h2 := mul_le_mul h1 (hγ s hs') (abs_nonneg _) (by positivity)
      calc φ s * (|a.eval t - a.eval s| * |x s|) ≤ φ s * (L / v * γ) :=
            mul_le_mul_of_nonneg_left h2 (hφ0 s)
        _ = (L * γ / v) * φ s := by ring
    · have : φ s = 0 := by
        rw [hφ, mol_J_zero _ (not_lt.mp hlt), mul_zero]
      rw [this]; simp
  have hbi : IntervalIntegrable (fun s => (L * γ / v) * φ s) volume 0 1 :=
    (mol_intOn _ (measurable_const.mul hφm) ((L * γ / v) * (v * cJ)) (fun s _ => by
      rw [abs_of_nonneg (mul_nonneg (by positivity) (hφ0 s))]
      exact mul_le_mul_of_nonneg_left (hφb s) (by positivity)))
  have := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hbound) hbi
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  rw [intervalIntegral.integral_const_mul]
  calc L * γ / v * ∫ s in (0:ℝ)..1, φ s ≤ L * γ / v * 1 :=
        mul_le_mul_of_nonneg_left (by simp_rw [hφ]; exact mol_phi_int v hv t) (by positivity)
    _ = L * γ / v := mul_one _

lemma mol_glue_cont : Continuous (fun t : ℝ => expNegInvGlue (1 - t ^ 2)) :=
  (expNegInvGlue.contDiff (n := 0)).continuous.comp (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2)

lemma mol_I_pos : 0 < ∫ t in (-1:ℝ)..1, Real.exp (-1 / (1 - t ^ 2)) := by
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-1 / (1 - t ^ 2))) volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    have : IntegrableOn (fun t : ℝ => expNegInvGlue (1 - t ^ 2)) (Ioo (-1) 1) :=
      (mol_glue_cont.integrableOn_Icc (a := -1) (b := 1)).mono_set Ioo_subset_Icc_self
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioo
    have hp : 0 < 1 - t ^ 2 := by
      have := sq_lt_one_iff_abs_lt_one t |>.mpr (abs_lt.mpr ht)
      linarith
    show expNegInvGlue (1 - t ^ 2) = _
    unfold expNegInvGlue
    rw [if_neg (not_le.mpr hp), neg_div, one_div]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun x _ => Real.exp_pos _) (by norm_num)

lemma mol_Jint_eq_one : ∫ t, J t = 1 := by
  have h1 : ∫ t, J t = ∫ t in Ioc (-1:ℝ) 1, J t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply mol_J_zero
    by_contra h
    apply hx
    rw [not_le, abs_lt] at h
    exact ⟨h.1, h.2.le⟩
  have h2 : ∫ t in Ioc (-1:ℝ) 1, J t = cJ * ∫ t in (-1:ℝ)..1, Real.exp (-1 / (1 - t ^ 2)) := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_const_mul]
    rw [setIntegral_congr_set (Ioo_ae_eq_Ioc).symm]
    rw [setIntegral_congr_set (Ioo_ae_eq_Ioc).symm]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    simp only [J]
    rw [if_pos (abs_lt.mpr hx)]
  rw [h1, h2]
  unfold cJ
  rw [inv_mul_cancel₀ mol_I_pos.ne']

lemma mol_phi_total (v : ℕ) (hv : 1 ≤ v) (t : ℝ) :
    Integrable (fun s : ℝ => (v : ℝ) * J (v * (t - s))) ∧
      ∫ s, (v : ℝ) * J (v * (t - s)) = 1 := by
  have hv0 : (v : ℝ) ≠ 0 := by positivity
  have hvpos : (0:ℝ) < v := by positivity
  have hJ' : Integrable (fun u : ℝ => J (v * u)) := by
    have := mol_J_integrable.comp_mul_left' (g := J) hv0
    simpa using this
  constructor
  · exact (hJ'.comp_sub_left t).const_mul _
  · rw [integral_const_mul]
    have h1 : ∫ s, J (v * (t - s)) = ∫ s, J (v * s) :=
      integral_sub_left_eq_self (fun u => J (v * u)) volume t
    rw [h1, Measure.integral_comp_mul_left J (v : ℝ), mol_Jint_eq_one]
    simp [hvpos.ne']

lemma mol_cont (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ M : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ M) (v : ℕ) : Continuous (Mv v f) := by
  obtain ⟨M, hM⟩ := hfb
  unfold Mv
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => v * cJ * M)
  · intro t
    exact ((mol_phi_meas v t).mul hf).aestronglyMeasurable
  · intro t
    refine Eventually.of_forall (fun s hs => ?_)
    have hs' : s ∈ Icc (0:ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (by positivity) (mol_J_nonneg _))]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (mol_J_le _) (by positivity)) (hM s hs')
      (abs_nonneg _) (by positivity [mol_cJ_nonneg])
  · exact intervalIntegrable_const
  · refine Eventually.of_forall (fun s _ => ?_)
    exact (continuous_const.mul (mol_J_cont.comp (continuous_const.mul
      (continuous_id.sub continuous_const)))).mul continuous_const

lemma mol_ball_vol (v : ℕ) (hv : 1 ≤ v) (t : ℝ) :
    volume.real (Metric.closedBall t (1 / (v:ℝ))) = 2 / v := by
  have hvpos : (0:ℝ) < v := by positivity
  rw [Real.volume_real_closedBall (by positivity)]
  ring

lemma mol_Mv_eq (f : ℝ → ℝ) (v : ℕ) (t : ℝ) :
    Mv v f t = ∫ s, ((v : ℝ) * J (v * (t - s))) * (Set.indicator (Icc (0:ℝ) 1) f s) := by
  unfold Mv
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  congr 1; ext s
  by_cases hs : s ∈ Icc (0:ℝ) 1
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

lemma mol_key (F : ℝ → ℝ) (hF : Measurable F) (M : ℝ) (hM : ∀ s, |F s| ≤ M) (v : ℕ) (hv : 1 ≤ v)
    (t : ℝ) :
    |(∫ s, ((v : ℝ) * J (v * (t - s))) * F s) - F t|
        ≤ 2 * cJ * ⨍ y in Metric.closedBall t (1 / (v:ℝ)), ‖F y - F t‖ ∧
    |(∫ s, ((v : ℝ) * J (v * (t - s))) * F s) - F t| ≤ 2 * M := by
  have hvpos : (0:ℝ) < v := by positivity
  obtain ⟨hφi, hφ1⟩ := mol_phi_total v hv t
  set φ : ℝ → ℝ := fun s => (v : ℝ) * J (v * (t - s)) with hφdef
  have hφ0 : ∀ s, 0 ≤ φ s := fun s => mul_nonneg hvpos.le (mol_J_nonneg _)
  have hφm : Measurable φ := mol_phi_meas v t
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hφF : Integrable (fun s => φ s * F s) := by
    refine (hφi.const_mul M).mono' (hφm.mul hF).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 s)]
    calc φ s * |F s| ≤ φ s * M := mul_le_mul_of_nonneg_left (hM s) (hφ0 s)
      _ = M * φ s := mul_comm _ _
  have hg : Integrable (fun s => φ s * (F s - F t)) := by
    have : (fun s => φ s * (F s - F t)) = fun s => φ s * F s - F t * φ s := by
      ext s; ring
    rw [this]
    exact hφF.sub (hφi.const_mul _)
  have e : (∫ s, φ s * F s) - F t = ∫ s, φ s * (F s - F t) := by
    have : (fun s => φ s * (F s - F t)) = fun s => φ s * F s - F t * φ s := by
      ext s; ring
    rw [this, integral_sub hφF (hφi.const_mul _), integral_const_mul, hφ1]; ring
  rw [e]
  have habs : |∫ s, φ s * (F s - F t)| ≤ ∫ s, |φ s * (F s - F t)| := by
    have := abs_integral_le_integral_abs (f := fun s => φ s * (F s - F t)) (μ := volume)
    simpa using this
  constructor
  · refine habs.trans ?_
    set B := Metric.closedBall t (1 / (v:ℝ)) with hB
    have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
    have hGi : Integrable (Set.indicator B (fun s => (v:ℝ) * cJ * ‖F s - F t‖)) := by
      rw [integrable_indicator_iff hBm]
      refine Measure.integrableOn_of_bounded (M := (v:ℝ) * cJ * (2 * M)) ?_ ?_ ?_
      · exact (measure_closedBall_lt_top).ne
      · exact (measurable_const.mul ((hF.sub measurable_const).norm)).aestronglyMeasurable
      · refine Eventually.of_forall fun s => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [mol_cJ_nonneg])]
        have : ‖F s - F t‖ ≤ 2 * M := by
          rw [Real.norm_eq_abs]
          calc |F s - F t| ≤ |F s| + |F t| := abs_sub _ _
            _ ≤ 2 * M := by linarith [hM s, hM t]
        exact mul_le_mul_of_nonneg_left this (by positivity [mol_cJ_nonneg])
    have hle : ∫ s, |φ s * (F s - F t)| ≤ ∫ s, Set.indicator B (fun s => (v:ℝ) * cJ * ‖F s - F t‖) s := by
      refine integral_mono hg.abs hGi (fun s => ?_)
      rw [abs_mul, abs_of_nonneg (hφ0 s)]
      by_cases hs : s ∈ B
      · rw [Set.indicator_of_mem hs, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [hφdef]
        exact mul_le_mul_of_nonneg_left (mol_J_le _) hvpos.le
      · rw [Set.indicator_of_notMem hs]
        have : φ s = 0 := by
          rw [hφdef]; simp only
          rw [mol_J_zero, mul_zero]
          rw [hB, Metric.mem_closedBall, Real.dist_eq, not_le] at hs
          rw [abs_mul, abs_of_pos hvpos, abs_sub_comm]
          rw [div_lt_iff₀ hvpos] at hs
          nlinarith
        rw [this]; simp
    refine hle.trans ?_
    rw [integral_indicator hBm, integral_const_mul, setAverage_eq, mol_ball_vol v hv t]
    simp only [smul_eq_mul]
    field_simp
    rfl
  · refine habs.trans ?_
    have h2 : ∀ s, |φ s * (F s - F t)| ≤ (2 * M) * φ s := by
      intro s
      rw [abs_mul, abs_of_nonneg (hφ0 s)]
      have : |F s - F t| ≤ 2 * M := by
        calc |F s - F t| ≤ |F s| + |F t| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hM s, hM t]
      nlinarith [hφ0 s, abs_nonneg (F s - F t)]
    calc ∫ s, |φ s * (F s - F t)| ≤ ∫ s, (2 * M) * φ s :=
          integral_mono hg.abs (hφi.const_mul _) h2
      _ = 2 * M := by rw [integral_const_mul, hφ1, mul_one]

lemma mol_leb (F : ℝ → ℝ) (hF : Integrable F) :
    ∀ᵐ t, Tendsto (fun v : ℕ => ⨍ y in Metric.closedBall t (1 / (v:ℝ)), ‖F y - F t‖) atTop (𝓝 0) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure ℝ)) hF.locallyIntegrable 1] with t ht
  refine ht (l := atTop) (fun _ : ℕ => t) (fun v : ℕ => 1 / (v:ℝ)) ?_ ?_
  · refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat 1, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with v hv
    have : (0:ℝ) < v := by exact_mod_cast hv
    simpa using this
  · exact Eventually.of_forall fun v => by simp [Metric.mem_closedBall]

theorem solution (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ M : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, |f t| ≤ M) :
    (∀ v : ℕ, Continuous (Mv v f)) ∧
    Tendsto (fun v : ℕ => ∫ t in (0:ℝ)..1, |Mv v f t - f t|) atTop (𝓝 0) := by
  refine ⟨mol_cont f hf hfb, ?_⟩
  obtain ⟨M, hM⟩ := hfb
  set F : ℝ → ℝ := Set.indicator (Icc (0:ℝ) 1) f with hFdef
  have hFm : Measurable F := hf.indicator measurableSet_Icc
  have hFb : ∀ s, |F s| ≤ M := by
    intro s
    by_cases hs : s ∈ Icc (0:ℝ) 1
    · rw [hFdef, Set.indicator_of_mem hs]; exact hM s hs
    · rw [hFdef, Set.indicator_of_notMem hs]
      simpa using le_trans (abs_nonneg _) (hM 0 ⟨le_refl _, zero_le_one⟩)
  have hFi : Integrable F := by
    rw [hFdef, integrable_indicator_iff measurableSet_Icc]
    refine Measure.integrableOn_of_bounded (M := M) (by simp) hf.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Eventually.of_forall fun s hs => by rw [Real.norm_eq_abs]; exact hM s hs
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_refl _, zero_le_one⟩)
  have hFeq : ∀ t ∈ Icc (0:ℝ) 1, F t = f t := fun t ht => by
    rw [hFdef, Set.indicator_of_mem ht]
  have hkey : ∀ v : ℕ, 1 ≤ v → ∀ t ∈ Icc (0:ℝ) 1,
      |Mv v f t - f t| ≤ 2 * cJ * ⨍ y in Metric.closedBall t (1 / (v:ℝ)), ‖F y - F t‖ ∧
      |Mv v f t - f t| ≤ 2 * M := by
    intro v hv t ht
    have := mol_key F hFm M hFb v hv t
    rw [← hFeq t ht, mol_Mv_eq]
    exact this
  have hmeas : ∀ᶠ v : ℕ in atTop, AEStronglyMeasurable (fun t => |Mv v f t - f t|)
      (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    refine Eventually.of_forall fun v => ?_
    exact (((mol_cont f hf ⟨M, hM⟩ v).aestronglyMeasurable).sub hf.aestronglyMeasurable).norm
  have hbd : ∀ᶠ v : ℕ in atTop, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 →
      ‖|Mv v f t - f t|‖ ≤ 2 * M := by
    refine Eventually.of_forall fun v => ?_
    refine Eventually.of_forall fun t ht => ?_
    have ht' : t ∈ Icc (0:ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_abs]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp [Mv]
      linarith [hM t ht']
    · exact (hkey v hv t ht').2
  have hlim : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 →
      Tendsto (fun v : ℕ => |Mv v f t - f t|) atTop (𝓝 0) := by
    filter_upwards [mol_leb F hFi] with t ht hts
    have ht' : t ∈ Icc (0:ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at hts; exact ⟨hts.1.le, hts.2⟩
    have h2 := ht.const_mul (2 * cJ)
    rw [mul_zero] at h2
    refine squeeze_zero' (Eventually.of_forall fun v => abs_nonneg _) ?_ h2
    filter_upwards [eventually_ge_atTop 1] with v hv
    have := (hkey v hv t ht').1
    simpa [Real.norm_eq_abs] using this
  have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := (0:ℝ)) (b := 1) (l := atTop) (F := fun (v : ℕ) t => |Mv v f t - f t|)
    (f := fun _ => (0:ℝ)) (fun _ => 2 * M) hmeas hbd intervalIntegrable_const hlim
  simpa using this
