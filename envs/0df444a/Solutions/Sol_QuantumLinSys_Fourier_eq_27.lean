-- Prove2me | solution 1 for QuantumLinSys.Fourier.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T20:31:07.720906+00:00
-- url     : https://prove2.me/submissions/582ffddb-ae76-4894-9086-ff85e4816a08

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting
import Theorems.Thm_QuantumLinSys_Fourier_eq_28

open MeasureTheory

theorem solution (x yJ zK : ℝ) (hx : x ≠ 0) (hy : 0 ≤ yJ) (hz : 0 ≤ zK) :
    ‖QuantumLinSys.Fourier.gTrunc yJ zK x - ((1 / x : ℝ) : ℂ)‖ ≤
      Real.exp (-(x * yJ) ^ 2 / 2) / |x| +
        2 * Real.exp (-zK ^ 2 / 2) / |x| := by
  let _ := hy
  let F : ℝ → ℝ → ℂ := fun y z =>
    (z : ℂ) * (Real.exp (-z ^ 2 / 2) : ℂ) * Complex.exp (-Complex.I * x * y * z)
  let E : ℝ → ℂ := fun z => (Real.exp (-z ^ 2 / 2) : ℂ)
  let e : ℝ → ℂ := fun z => Complex.exp (-Complex.I * x * yJ * z)
  have hF_cont : Continuous (Function.uncurry F) := by
    dsimp [Function.uncurry, F]
    fun_prop
  have hF_int : IntegrableOn (Function.uncurry F) (Set.uIoc 0 yJ ×ˢ Set.uIoc (-zK) zK) := by
    refine (hF_cont.continuousOn.integrableOn_compact
      ((isCompact_uIcc (a := (0 : ℝ)) (b := yJ)).prod
        (isCompact_uIcc (a := -zK) (b := zK)))).mono_set ?_
    exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  have h_swap :
      (∫ y in (0 : ℝ)..yJ, ∫ z in (-zK)..zK, F y z) =
        ∫ z in (-zK)..zK, ∫ y in (0 : ℝ)..yJ, F y z :=
    intervalIntegral_intervalIntegral_swap hF_int
  have h_inner (z : ℝ) :
      (∫ y in (0 : ℝ)..yJ, F y z) =
        E z * (1 - e z) / (Complex.I * (x : ℂ)) := by
    by_cases hz0 : z = 0
    · subst hz0
      simp [F, E, e]
    · have hc : -Complex.I * (x : ℂ) * (z : ℂ) ≠ 0 := by
        simp [Complex.I_ne_zero, hx, hz0]
      have hF_eq : ∀ y : ℝ, F y z =
          ((z : ℂ) * E z) * Complex.exp ((-Complex.I * (x : ℂ) * (z : ℂ)) * (y : ℂ)) := by
        intro y
        dsimp [F, E]
        ring_nf
      simp_rw [hF_eq, intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      have hzC : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz0
      have he_eq : Complex.exp (-Complex.I * (x : ℂ) * (z : ℂ) * (yJ : ℂ)) = e z := by
        dsimp [e]
        ring_nf
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, he_eq]
      field_simp [Complex.I_ne_zero, hxC, hzC]
      ring
  have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have h_sqrt_ne : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr h_sqrt_pos.ne'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hg_eq : QuantumLinSys.Fourier.gTrunc yJ zK x =
      (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
        ∫ z in (-zK)..zK, E z * (1 - e z) := by
    change (Complex.I / (Real.sqrt (2 * Real.pi) : ℂ)) *
        (∫ y in (0 : ℝ)..yJ, ∫ z in (-zK)..zK, F y z) = _
    rw [h_swap]
    simp_rw [h_inner, intervalIntegral.integral_div]
    field_simp [h_sqrt_ne, hxC, Complex.I_ne_zero]
  have h_gauss_real : ∫ z : ℝ, Real.exp (-z ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
    have h := integral_gaussian (1 / 2 : ℝ)
    have h_fn : (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2)) =
        (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
      ext z; ring_nf
    rw [h_fn] at h
    rw [h]
    congr 1
    ring
  have h_gauss_complex : ∫ z : ℝ, E z = (Real.sqrt (2 * Real.pi) : ℂ) := by
    have h : (fun z : ℝ => E z) = fun z : ℝ => (algebraMap ℝ ℂ) (Real.exp (-z ^ 2 / 2)) := rfl
    rw [h, integral_ofReal, h_gauss_real]
    rfl
  have h_inv_x : ((1 / x : ℝ) : ℂ) =
      (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) * ∫ z : ℝ, E z := by
    rw [h_gauss_complex]
    push_cast
    field_simp [h_sqrt_ne, hxC]
  have hE_int : Integrable E volume := by
    have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).ofReal (𝕜 := ℂ)
    convert h using 1
    ext z
    dsimp [E]
    ring_nf
  have hEe_int : Integrable (fun z => E z * e z) volume := by
    refine Integrable.mono' hE_int.norm ?_ ?_
    · dsimp [E, e]; fun_prop
    · filter_upwards with z
      have hre : (-Complex.I * (x : ℂ) * (yJ : ℂ) * (z : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im]
      dsimp [E, e]
      rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
  have h_split_univ : ∀ (f : ℝ → ℂ), Integrable f →
      (∫ z : ℝ, f z) =
        (∫ z in Set.Iic (-zK), f z) + (∫ z in (-zK)..zK, f z) +
          (∫ z in Set.Ioi zK, f z) := by
    intro f hf
    have hle : -zK ≤ zK := by linarith
    rw [intervalIntegral.integral_of_le hle]
    have h1 : (∫ z in Set.Iic zK, f z) =
        (∫ z in Set.Iic (-zK), f z) + (∫ z in Set.Ioc (-zK) zK, f z) := by
      rw [← setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        hf.integrableOn hf.integrableOn, Set.Iic_union_Ioc_eq_Iic hle]
    have h2 : (∫ z : ℝ, f z) = (∫ z in Set.Iic zK, f z) + (∫ z in Set.Ioi zK, f z) :=
      (intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn).symm
    rw [h2, h1]
  have h_int_sub :
      (∫ z in (-zK)..zK, E z * (1 - e z)) - (∫ z : ℝ, E z) =
        -(∫ z : ℝ, E z * e z) +
          (∫ z in Set.Iic (-zK), E z * (e z - 1)) +
          (∫ z in Set.Ioi zK, E z * (e z - 1)) := by
    have h_cont_1 : Continuous (fun z : ℝ => E z) := by dsimp [E]; fun_prop
    have h_cont_2 : Continuous (fun z : ℝ => E z * e z) := by dsimp [E, e]; fun_prop
    have h_sub_interval :
        (∫ z in (-zK)..zK, E z * (1 - e z)) =
          (∫ z in (-zK)..zK, E z) - (∫ z in (-zK)..zK, E z * e z) := by
      simp_rw [mul_sub, mul_one]
      exact intervalIntegral.integral_sub
        (h_cont_1.intervalIntegrable _ _) (h_cont_2.intervalIntegrable _ _)
    have h_sub_Iic :
        (∫ z in Set.Iic (-zK), E z * (e z - 1)) =
          (∫ z in Set.Iic (-zK), E z * e z) - (∫ z in Set.Iic (-zK), E z) := by
      simp_rw [mul_sub, mul_one]
      exact integral_sub hEe_int.integrableOn hE_int.integrableOn
    have h_sub_Ioi :
        (∫ z in Set.Ioi zK, E z * (e z - 1)) =
          (∫ z in Set.Ioi zK, E z * e z) - (∫ z in Set.Ioi zK, E z) := by
      simp_rw [mul_sub, mul_one]
      exact integral_sub hEe_int.integrableOn hE_int.integrableOn
    rw [h_sub_interval, h_sub_Iic, h_sub_Ioi, h_split_univ E hE_int, h_split_univ _ hEe_int]
    ring
  have h_diff_eq :
      QuantumLinSys.Fourier.gTrunc yJ zK x - ((1 / x : ℝ) : ℂ) =
        (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
          (-(∫ z : ℝ, E z * e z) +
            (∫ z in Set.Iic (-zK), E z * (e z - 1)) +
            (∫ z in Set.Ioi zK, E z * (e z - 1))) := by
    rw [hg_eq, h_inv_x, ← mul_sub, h_int_sub]
  have h_fourier_eq :
      (∫ z : ℝ, E z * e z) =
        (Real.sqrt (2 * Real.pi) : ℂ) * (Real.exp (-(x * yJ) ^ 2 / 2) : ℂ) := by
    have h_fn : (fun z : ℝ => E z * e z) =
        fun z : ℝ => Complex.exp (Complex.I * ((-(x * yJ) : ℝ) : ℂ) * (z : ℂ)) *
          Complex.exp (-(1 / 2 : ℂ) * (z : ℂ) ^ 2) := by
      ext z
      dsimp [E, e]
      rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h_fn, fourierIntegral_gaussian (b := (1 / 2 : ℂ)) (by norm_num) ((-(x * yJ) : ℝ) : ℂ)]
    have h1 : ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (2 * Real.pi) : ℂ) := by
      have h_eq : (Real.pi : ℂ) / (1 / 2 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
        push_cast; ring
      have h_pow : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [h_eq, h_pow, ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]
    have h2 : Complex.exp (-(((-(x * yJ) : ℝ) : ℂ) ^ 2) / (4 * (1 / 2 : ℂ))) =
        (Real.exp (-(x * yJ) ^ 2 / 2) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [h1, h2]
  have h_norm_fourier :
      ‖∫ z : ℝ, E z * e z‖ = Real.sqrt (2 * Real.pi) * Real.exp (-(x * yJ) ^ 2 / 2) := by
    rw [h_fourier_eq, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg h_sqrt_pos.le, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h_tail_pt : ∀ z : ℝ, ‖E z * (e z - 1)‖ ≤ 2 * Real.exp (-z ^ 2 / 2) := by
    intro z
    have hre : (-Complex.I * (x : ℂ) * (yJ : ℂ) * (z : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have he_norm : ‖e z‖ = 1 := by
      dsimp [e]
      rw [Complex.norm_exp, hre, Real.exp_zero]
    have hsub : ‖e z - 1‖ ≤ 2 := by
      calc ‖e z - 1‖ ≤ ‖e z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [he_norm, norm_one]; norm_num
    dsimp [E]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-z ^ 2 / 2) * ‖e z - 1‖
        ≤ Real.exp (-z ^ 2 / 2) * 2 :=
          mul_le_mul_of_nonneg_left hsub (Real.exp_pos _).le
      _ = 2 * Real.exp (-z ^ 2 / 2) := by ring
  have h_exp_real_int : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
    have h := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    convert h using 1
    ext z; ring_nf
  have h_tail_Ioi :
      ‖∫ z in Set.Ioi zK, E z * (e z - 1)‖ ≤ 2 * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := by
    calc ‖∫ z in Set.Ioi zK, E z * (e z - 1)‖
        ≤ ∫ z in Set.Ioi zK, ‖E z * (e z - 1)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z in Set.Ioi zK, 2 * Real.exp (-z ^ 2 / 2) := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi (fun z _ => h_tail_pt z)
          · exact (hEe_int.sub hE_int).norm.integrableOn.congr_fun
              (fun z _ => by simp only [Pi.sub_apply, mul_sub, mul_one]) measurableSet_Ioi
          · exact (h_exp_real_int.const_mul 2).integrableOn
      _ = 2 * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := integral_const_mul _ _
  have h_Iic_eq_Ioi :
      (∫ z in Set.Iic (-zK), Real.exp (-z ^ 2 / 2)) =
        ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := by
    have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
    have hpre : Neg.neg ⁻¹' Set.Iic (-zK) = Set.Ici zK := by
      ext z; simp
    have h1 : (∫ z in Set.Iic (-zK), Real.exp (-z ^ 2 / 2)) =
        ∫ z in Set.Ici zK, Real.exp (-z ^ 2 / 2) := by
      rw [← hmp.setIntegral_preimage_emb (Homeomorph.neg ℝ).measurableEmbedding
        (fun z => Real.exp (-z ^ 2 / 2)) (Set.Iic (-zK)), hpre]
      congr 1
      ext z
      simp
    rw [h1]
    exact (setIntegral_congr_set Ioi_ae_eq_Ici).symm
  have h_tail_Iic :
      ‖∫ z in Set.Iic (-zK), E z * (e z - 1)‖ ≤ 2 * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := by
    calc ‖∫ z in Set.Iic (-zK), E z * (e z - 1)‖
        ≤ ∫ z in Set.Iic (-zK), ‖E z * (e z - 1)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z in Set.Iic (-zK), 2 * Real.exp (-z ^ 2 / 2) := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Iic (fun z _ => h_tail_pt z)
          · exact (hEe_int.sub hE_int).norm.integrableOn.congr_fun
              (fun z _ => by simp only [Pi.sub_apply, mul_sub, mul_one]) measurableSet_Iic
          · exact (h_exp_real_int.const_mul 2).integrableOn
      _ = 2 * ∫ z in Set.Iic (-zK), Real.exp (-z ^ 2 / 2) := integral_const_mul _ _
      _ = 2 * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := by rw [h_Iic_eq_Ioi]
  have h_eq28 := QuantumLinSys.Fourier.eq_28 zK hz
  have h_pref_norm :
      ‖(1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ)))‖ =
        1 / (Real.sqrt (2 * Real.pi) * |x|) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg h_sqrt_pos.le, Real.norm_eq_abs]
  rw [h_diff_eq, norm_mul, h_pref_norm]
  have h_tri :
      ‖-(∫ z : ℝ, E z * e z) +
          (∫ z in Set.Iic (-zK), E z * (e z - 1)) +
          (∫ z in Set.Ioi zK, E z * (e z - 1))‖ ≤
        Real.sqrt (2 * Real.pi) * Real.exp (-(x * yJ) ^ 2 / 2) +
          4 * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := by
    calc ‖-(∫ z : ℝ, E z * e z) +
            (∫ z in Set.Iic (-zK), E z * (e z - 1)) +
            (∫ z in Set.Ioi zK, E z * (e z - 1))‖
        ≤ ‖-(∫ z : ℝ, E z * e z) + (∫ z in Set.Iic (-zK), E z * (e z - 1))‖ +
            ‖∫ z in Set.Ioi zK, E z * (e z - 1)‖ := norm_add_le _ _
      _ ≤ (‖-(∫ z : ℝ, E z * e z)‖ + ‖∫ z in Set.Iic (-zK), E z * (e z - 1)‖) +
            ‖∫ z in Set.Ioi zK, E z * (e z - 1)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ = ‖∫ z : ℝ, E z * e z‖ + ‖∫ z in Set.Iic (-zK), E z * (e z - 1)‖ +
            ‖∫ z in Set.Ioi zK, E z * (e z - 1)‖ := by rw [norm_neg]
      _ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(x * yJ) ^ 2 / 2) +
            2 * (∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2)) +
            2 * (∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2)) := by
          rw [← h_norm_fourier]
          exact add_le_add (add_le_add le_rfl h_tail_Iic) h_tail_Ioi
      _ = Real.sqrt (2 * Real.pi) * Real.exp (-(x * yJ) ^ 2 / 2) +
            4 * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := by ring
  have h_pref_nonneg : 0 ≤ 1 / (Real.sqrt (2 * Real.pi) * |x|) := by positivity
  calc 1 / (Real.sqrt (2 * Real.pi) * |x|) *
        ‖-(∫ z : ℝ, E z * e z) +
          (∫ z in Set.Iic (-zK), E z * (e z - 1)) +
          (∫ z in Set.Ioi zK, E z * (e z - 1))‖
      ≤ 1 / (Real.sqrt (2 * Real.pi) * |x|) *
          (Real.sqrt (2 * Real.pi) * Real.exp (-(x * yJ) ^ 2 / 2) +
            4 * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left h_tri h_pref_nonneg
    _ = Real.exp (-(x * yJ) ^ 2 / 2) / |x| +
          (4 / |x|) * (1 / Real.sqrt (2 * Real.pi) * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2)) := by
        field_simp [h_sqrt_pos.ne', abs_ne_zero.mpr hx]
    _ ≤ Real.exp (-(x * yJ) ^ 2 / 2) / |x| + (4 / |x|) * (1 / 2 * Real.exp (-zK ^ 2 / 2)) := by
        gcongr
    _ = Real.exp (-(x * yJ) ^ 2 / 2) / |x| + 2 * Real.exp (-zK ^ 2 / 2) / |x| := by
        ring
