-- Prove2me | solution 1 for TVSDP.PolyOpt.lemma_3b
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:28:06.82236+00:00
-- url     : https://prove2.me/submissions/c73feab4-2301-4a2b-9431-facdb0d401cb

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

theorem solution (a : Polynomial ℝ) (x : ℝ → ℝ) (hx : Measurable x)
    (hxb : ∃ M : ℝ, ∀ t ∈ Set.Icc (0:ℝ) 1, |x t| ≤ M) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ v : ℕ in atTop, ∀ t ∈ Set.Icc (0:ℝ) 1,
      |a.eval t * Mv v x t - Mv v (fun s => a.eval s * x s) t| ≤ δ := by
  intro δ hδ
  obtain ⟨M, hM⟩ := hxb
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (a.derivative.continuous.continuousOn)
  have hL : ∀ t ∈ Set.Icc (0:ℝ) 1, |a.derivative.eval t| ≤ C := fun t ht => by
    simpa using hC t ht
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈C * M / δ⌉₊] with v hv1 hv2 t ht
  refine (mol_rate a x hx C M hL hM v hv1 t ht).trans ?_
  have hvpos : (0:ℝ) < v := by exact_mod_cast hv1
  rw [div_le_iff₀ hvpos]
  have h1 : C * M / δ ≤ v := (Nat.le_ceil _).trans (by exact_mod_cast hv2)
  rw [div_le_iff₀ hδ] at h1
  linarith
