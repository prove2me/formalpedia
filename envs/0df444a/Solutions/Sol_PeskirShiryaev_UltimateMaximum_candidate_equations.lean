-- Prove2me | solution 1 for PeskirShiryaev.UltimateMaximum.candidate_equations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:55:16.706614+00:00
-- url     : https://prove2.me/submissions/8edd86cf-9ab0-4121-a0ef-56b491d9de9b

import Mathlib
import Definitions.Def_PeskirShiryaev_UltimateMaximum_gaussianBoundary

open MeasureTheory Set Filter Topology
open PeskirShiryaev.UltimateMaximum

lemma s225mb_phi_eq : phi = fun x => Real.exp (-(1 / 2 : ℝ) * x ^ 2) / Real.sqrt (2 * Real.pi) := by
  funext x; unfold phi; congr 2; ring

lemma s225mb_phi_cont : Continuous phi := by
  rw [s225mb_phi_eq]; fun_prop

lemma s225mb_phi_pos (x : ℝ) : 0 < phi x := by
  unfold phi; positivity

lemma s225mb_phi_int : Integrable phi := by
  rw [s225mb_phi_eq]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).div_const _

lemma s225mb_phi_total : ∫ x, phi x = 1 := by
  rw [s225mb_phi_eq]
  simp only
  rw [integral_div, integral_gaussian]
  have : Real.pi / (1 / 2) = 2 * Real.pi := by ring
  rw [this, div_self]
  positivity

lemma s225mb_phi_even (x : ℝ) : phi (-x) = phi x := by
  unfold phi; rw [neg_sq]

lemma s225mb_Phi0 : Phi 0 = 1 / 2 := by
  have h1 : (∫ x in Iic (0 : ℝ), phi x) = ∫ x in Ioi (0 : ℝ), phi x := by
    have := integral_comp_neg_Iic (0 : ℝ) phi
    simp only [neg_zero, s225mb_phi_even] at this
    exact this
  have h2 := intervalIntegral.integral_Iic_add_Ioi (f := phi) (b := 0) (μ := volume)
    s225mb_phi_int.integrableOn s225mb_phi_int.integrableOn
  rw [s225mb_phi_total, ← h1] at h2
  unfold Phi; linarith

lemma s225mb_Phi_eq (y : ℝ) : Phi y = Phi 0 + ∫ x in (0 : ℝ)..y, phi x := by
  unfold Phi
  rw [← intervalIntegral.integral_Iic_sub_Iic s225mb_phi_int.integrableOn
    s225mb_phi_int.integrableOn]
  ring

lemma s225mb_Phi_deriv (y : ℝ) : HasDerivAt Phi (phi y) y := by
  have : Phi = fun y => Phi 0 + ∫ x in (0 : ℝ)..y, phi x := funext s225mb_Phi_eq
  rw [this]
  exact ((s225mb_phi_cont.integral_hasStrictDerivAt 0 y).hasDerivAt).const_add _

lemma s225mb_Phi_cont : Continuous Phi :=
  continuous_iff_continuousAt.mpr fun y => (s225mb_Phi_deriv y).continuousAt

lemma s225mb_phi_deriv (x : ℝ) : HasDerivAt phi (-x * phi x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x :=
    (((hasDerivAt_pow 2 x).neg).div_const 2).congr_deriv (by push_cast; ring)
  have h2 := h1.exp.div_const (Real.sqrt (2 * Real.pi))
  unfold phi
  exact h2.congr_deriv (by ring)

lemma s225mb_Phi_top : Tendsto Phi atTop (𝓝 1) := by
  have h := tendsto_setIntegral_of_monotone (μ := volume) (f := phi) (s := fun x : ℝ => Iic x)
    (fun i => measurableSet_Iic) (fun a b hab => Iic_subset_Iic.mpr hab)
    s225mb_phi_int.integrableOn
  rw [iUnion_Iic, Measure.restrict_univ, s225mb_phi_total] at h
  exact h

lemma s225mb_xphi_top : Tendsto (fun x => x * phi x) atTop (𝓝 0) := by
  set c := Real.sqrt (2 * Real.pi)
  have hc : 0 < c := by positivity
  have hu : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu).div_const c
  rw [zero_div] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with x hx
    exact mul_nonneg hx (s225mb_phi_pos x).le
  · filter_upwards [eventually_ge_atTop 2] with x hx
    simp only [Function.comp_apply, pow_one]
    unfold phi
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hc.le
    have he : 0 < Real.exp (-(x ^ 2) / 2) := Real.exp_pos _
    have : Real.exp (-(x ^ 2 / 2)) = Real.exp (-(x ^ 2) / 2) := by congr 1; ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ he.le
    nlinarith

lemma s225mb_R_deriv (z : ℝ) : HasDerivAt rootEquation (2 * phi z * (1 + z ^ 2)) z := by
  have h := ((((s225mb_Phi_deriv z).const_mul 4).sub
    (((hasDerivAt_id' z).const_mul 2).mul (s225mb_phi_deriv z))).sub_const 3)
  unfold rootEquation
  exact h.congr_deriv (by ring)

lemma s225mb_R_mono : StrictMono rootEquation :=
  strictMono_of_hasDerivAt_pos s225mb_R_deriv fun z => by
    have := s225mb_phi_pos z; positivity

lemma s225mb_R_cont : Continuous rootEquation :=
  continuous_iff_continuousAt.mpr fun y => (s225mb_R_deriv y).continuousAt

lemma s225mb_R0 : rootEquation 0 = -1 := by
  unfold rootEquation; rw [s225mb_Phi0]; ring

lemma s225mb_root : ∃ z0, 0 < z0 ∧ rootEquation z0 = 0 := by
  have hlim : Tendsto rootEquation atTop (𝓝 1) := by
    have := ((s225mb_Phi_top.const_mul 4).sub (s225mb_xphi_top.const_mul 2)).sub_const 3
    unfold rootEquation
    convert this using 2
    · ring
    · norm_num
  obtain ⟨M, hM⟩ := (hlim.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists_forall_of_atTop
  set M' := max M 1
  have hM' := hM M' (le_max_left _ _)
  have hM0 : (0 : ℝ) ≤ M' := le_trans zero_le_one (le_max_right _ _)
  obtain ⟨z0, hz0, hz⟩ := intermediate_value_Icc hM0 s225mb_R_cont.continuousOn
    (show (0 : ℝ) ∈ Icc (rootEquation 0) (rootEquation M') by
      rw [s225mb_R0]; exact ⟨by norm_num, hM'.le⟩)
  refine ⟨z0, ?_, hz⟩
  rcases eq_or_lt_of_le hz0.1 with h | h
  · rw [← h, s225mb_R0] at hz; norm_num at hz
  · exact h

lemma s225mb_crit : 0 < criticalLevel ∧ rootEquation criticalLevel = 0 := by
  obtain ⟨z0, hz0, hz⟩ := s225mb_root
  have : {z : ℝ | 0 ≤ z ∧ rootEquation z = 0} = {z0} := by
    ext z
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨-, h⟩; exact s225mb_R_mono.injective (h.trans hz.symm)
    · rintro rfl; exact ⟨hz0.le, hz⟩
  unfold criticalLevel
  rw [this, csInf_singleton]
  exact ⟨hz0, hz⟩

/-- gluing one-sided derivatives -/
lemma s225mb_glue (F L R : ℝ → ℝ) (a d : ℝ) (hL : HasDerivAt L d a) (hR : HasDerivAt R d a)
    (hFL : F =ᶠ[𝓝[≤] a] L) (hFR : F =ᶠ[𝓝[≥] a] R) (hLa : F a = L a) (hRa : F a = R a) :
    HasDerivAt F d a := by
  have h1 := hL.hasDerivWithinAt.congr_of_eventuallyEq hFL hLa
  have h2 := hR.hasDerivWithinAt.congr_of_eventuallyEq hFR hRa
  have := h1.union h2
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
  exact this

theorem solution :
    0 < criticalLevel ∧ rootEquation criticalLevel = 0 ∧
    (∀ z : ℝ, rootEquation z = 0 → z = criticalLevel) ∧
    ContDiff ℝ 1 candidate ∧
    (∀ z : ℝ, |z| < criticalLevel →
      DifferentiableAt ℝ (deriv candidate) z ∧
      deriv (deriv candidate) z + z * deriv candidate z - 2 * candidate z =
        -runningCost |z|) ∧
    candidate criticalLevel = 0 ∧ candidate (-criticalLevel) = 0 ∧
    deriv candidate criticalLevel = 0 ∧ deriv candidate (-criticalLevel) = 0 ∧
    deriv candidate 0 = 0 := by
  obtain ⟨hzpos, hzroot⟩ := s225mb_crit
  set zs := criticalLevel with hzs
  set Ps := Phi zs with hPs
  set f : ℝ → ℝ := fun w => Ps * (1 + w ^ 2) - w * phi w + (1 - w ^ 2) * Phi w - 3 / 2 with hf
  set D : ℝ → ℝ := fun w => 2 * w * (Ps - Phi w) with hDdef
  have hfd : ∀ w, HasDerivAt f (D w) w := by
    intro w
    have h := ((((hasDerivAt_pow 2 w).const_add 1).const_mul Ps).sub
      ((hasDerivAt_id' w).mul (s225mb_phi_deriv w))).add
      (((hasDerivAt_pow 2 w).const_sub 1).mul (s225mb_Phi_deriv w)) |>.sub_const (3 / 2)
    exact h.congr_deriv (by simp only [hDdef]; push_cast; ring)
  have hDd : ∀ w, HasDerivAt D (2 * (Ps - Phi w) - 2 * w * phi w) w := by
    intro w
    have h := ((hasDerivAt_id' w).const_mul 2).mul ((s225mb_Phi_deriv w).const_sub Ps)
    exact h.congr_deriv (by ring)
  have hfz : f zs = 0 := by
    show Ps * (1 + zs ^ 2) - zs * phi zs + (1 - zs ^ 2) * Phi zs - 3 / 2 = 0
    unfold rootEquation at hzroot
    linear_combination (1 / 2 : ℝ) * hzroot
  have hC : candidate = fun z => if |z| ≤ zs then f |z| else 0 := by
    funext z
    unfold candidate
    simp only [hf, sq_abs, hzs, hPs]
  have hCeven : ∀ z, candidate (-z) = candidate z := by
    intro z; rw [hC]; simp only [abs_neg]
  set Cd : ℝ → ℝ := fun z => if |z| ≤ zs then 2 * z * (Ps - Phi |z|) else 0 with hCd
  have hCdodd : ∀ z, Cd (-z) = -Cd z := by
    intro z; simp only [hCd, abs_neg]; split_ifs <;> ring
  have hD0 : D 0 = 0 := by simp [hDdef]
  have hDzs : D zs = 0 := by simp [hDdef, hPs]
  -- derivative for z ≥ 0
  have hpos : ∀ z, 0 ≤ z → HasDerivAt candidate (Cd z) z := by
    intro z hz
    rcases eq_or_lt_of_le hz with h0 | h0
    · -- z = 0
      subst h0
      have hCd0 : Cd 0 = 0 := by simp [hCd]
      rw [hCd0]
      have hL : HasDerivAt (fun x => f (-x)) 0 0 := by
        have := (hfd (-0)).comp 0 (hasDerivAt_neg 0)
        rw [neg_zero, hD0, zero_mul] at this
        exact this
      have hR : HasDerivAt f 0 0 := by have := hfd 0; rwa [hD0] at this
      refine s225mb_glue _ _ _ 0 0 hL hR ?_ ?_ ?_ ?_
      · filter_upwards [Ioc_mem_nhdsLE (show -zs < 0 by linarith)] with x hx
        rw [hC]; simp only
        rw [if_pos (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]),
          abs_of_nonpos hx.2]
      · filter_upwards [Ico_mem_nhdsGE hzpos] with x hx
        rw [hC]; simp only
        rw [if_pos (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]),
          abs_of_nonneg hx.1]
      · rw [hC]; simp [hzpos.le]
      · rw [hC]; simp [hzpos.le]
    · rcases lt_trichotomy z zs with h1 | h1 | h1
      · have hev : candidate =ᶠ[𝓝 z] f := by
          filter_upwards [Ioo_mem_nhds h0 h1] with x hx
          rw [hC]; simp only
          rw [abs_of_pos hx.1, if_pos hx.2.le]
        have : Cd z = D z := by
          simp only [hCd, hDdef]; rw [abs_of_pos h0, if_pos h1.le]
        rw [this]
        exact (hfd z).congr_of_eventuallyEq hev
      · subst h1
        have : Cd zs = 0 := by
          simp only [hCd]; rw [abs_of_pos h0, if_pos le_rfl]; simp [hPs]
        rw [this]
        have hR : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 zs := hasDerivAt_const _ _
        have hL : HasDerivAt f 0 zs := by have := hfd zs; rwa [hDzs] at this
        refine s225mb_glue _ _ _ zs 0 hL hR ?_ ?_ ?_ ?_
        · filter_upwards [Ioc_mem_nhdsLE h0] with x hx
          rw [hC]; simp only
          rw [abs_of_pos hx.1, if_pos hx.2]
        · filter_upwards [self_mem_nhdsWithin] with x hx
          rw [hC]; simp only
          rw [mem_Ici] at hx
          rw [abs_of_pos (lt_of_lt_of_le h0 hx)]
          split_ifs with h
          · rw [le_antisymm h hx, hfz]
          · rfl
        · rw [hC]; simp only; rw [abs_of_pos h0, if_pos le_rfl]
        · rw [hC]; simp only; rw [abs_of_pos h0, if_pos le_rfl, hfz]
      · have hev : candidate =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [Ioi_mem_nhds h1] with x hx
          rw [hC]; simp only
          rw [if_neg (by rw [abs_of_pos (lt_trans hzpos hx)]; exact not_le.mpr hx)]
        have : Cd z = 0 := by
          simp only [hCd]; rw [if_neg (by rw [abs_of_pos h0]; exact not_le.mpr h1)]
        rw [this]
        exact (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq hev
  have hderiv : ∀ z, HasDerivAt candidate (Cd z) z := by
    intro z
    rcases le_or_gt 0 z with hz | hz
    · exact hpos z hz
    · have h := (hpos (-z) (by linarith)).comp z (hasDerivAt_neg z)
      have hfun : candidate ∘ (fun x => -x) = candidate := by
        funext x; simp only [Function.comp_apply]; exact hCeven x
      rw [hfun, hCdodd] at h
      exact h.congr_deriv (by ring)
  have hdC : deriv candidate = Cd := funext fun z => (hderiv z).deriv
  -- second derivative inside
  set D2 : ℝ → ℝ := fun z => 2 * (Ps - Phi |z|) - 2 * |z| * phi |z| with hD2
  have hEq : ∀ z, |z| ≤ zs → Cd z = 2 * z * (Ps - Phi |z|) := by
    intro z hz; simp only [hCd]; rw [if_pos hz]
  have hpos2 : ∀ z, 0 ≤ z → z < zs → HasDerivAt Cd (D2 z) z := by
    intro z hz hzz
    rcases eq_or_lt_of_le hz with h0 | h0
    · subst h0
      have hL : HasDerivAt (fun x => -D (-x)) (D2 0) 0 := by
        have := ((hDd (-0)).comp 0 (hasDerivAt_neg 0)).neg
        exact this.congr_deriv (by rw [hD2]; simp)
      have hR : HasDerivAt D (D2 0) 0 := by
        exact (hDd 0).congr_deriv (by rw [hD2]; simp)
      refine s225mb_glue _ _ _ 0 _ hL hR ?_ ?_ ?_ ?_
      · filter_upwards [Ioc_mem_nhdsLE (show -zs < 0 by linarith)] with x hx
        rw [hEq x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]),
          abs_of_nonpos hx.2]
        simp only [hDdef]; ring
      · filter_upwards [Ico_mem_nhdsGE hzpos] with x hx
        rw [hEq x (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]),
          abs_of_nonneg hx.1]
      · simp [hCd, hDdef, hzpos.le]
      · simp [hCd, hDdef, hzpos.le]
    · have hev : Cd =ᶠ[𝓝 z] D := by
        filter_upwards [Ioo_mem_nhds h0 hzz] with x hx
        rw [hEq x (by rw [abs_of_pos hx.1]; exact hx.2.le), abs_of_pos hx.1]
      have : D2 z = 2 * (Ps - Phi z) - 2 * z * phi z := by
        simp only [hD2]; rw [abs_of_pos h0]
      rw [this]
      exact (hDd z).congr_of_eventuallyEq hev
  have hderiv2 : ∀ z, |z| < zs → HasDerivAt Cd (D2 z) z := by
    intro z hz
    rcases le_or_gt 0 z with h | h
    · exact hpos2 z h (by rwa [abs_of_nonneg h] at hz)
    · have hh := (hpos2 (-z) (by linarith) (by rw [abs_of_neg h] at hz; exact hz)).comp z
        (hasDerivAt_neg z)
      have hfun : Cd ∘ (fun x => -x) = fun x => -Cd x := by
        funext x; simp only [Function.comp_apply]; exact hCdodd x
      rw [hfun] at hh
      have h3 : HasDerivAt Cd (-(D2 (-z) * -1)) z :=
        hh.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp)
      exact h3.congr_deriv (by simp only [hD2, abs_neg]; ring)
  -- continuity of Cd
  have hCdc : Continuous Cd := by
    have : Cd = fun z => 2 * z * (Ps - Phi (min |z| zs)) := by
      funext z
      simp only [hCd]
      split_ifs with h
      · rw [min_eq_left h]
      · rw [min_eq_right (not_le.mp h).le]; simp [hPs]
    rw [this]
    have := s225mb_Phi_cont
    fun_prop
  refine ⟨hzpos, hzroot, fun z hz => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact s225mb_R_mono.injective (hz.trans hzroot.symm)
  · rw [contDiff_one_iff_deriv, hdC]
    exact ⟨fun z => (hderiv z).differentiableAt, hCdc⟩
  · intro z hz
    rw [hdC]
    refine ⟨(hderiv2 z hz).differentiableAt, ?_⟩
    rw [(hderiv2 z hz).deriv, hEq z hz.le, hC]
    simp only
    rw [if_pos hz.le]
    unfold runningCost
    simp only [hD2, hf]
    have hz2 : z * z = |z| ^ 2 := by rw [sq_abs]; ring
    linear_combination (2 * (Ps - Phi |z|)) * hz2
  · rw [hC]; simp only; rw [abs_of_pos hzpos, if_pos le_rfl, hfz]
  · rw [hC]; simp only; rw [abs_neg, abs_of_pos hzpos, if_pos le_rfl, hfz]
  · rw [hdC]; simp only [hCd]; rw [abs_of_pos hzpos, if_pos le_rfl]; simp [hPs]
  · rw [hdC]; simp only [hCd]; rw [abs_neg, abs_of_pos hzpos, if_pos le_rfl]; simp [hPs]
  · rw [hdC]; simp [hCd]
