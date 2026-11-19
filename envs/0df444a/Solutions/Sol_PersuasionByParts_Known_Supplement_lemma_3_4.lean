-- Prove2me | solution 1 for PersuasionByParts.Known.Supplement.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:20:24.97989+00:00
-- url     : https://prove2.me/submissions/3279802f-e05b-4977-9a74-f9aa9397b490

import Mathlib

open MeasureTheory ProbabilityTheory Set

lemma chord_neg_rpow (r w : ℝ) (hr : 0 < r) (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2) :
    (1 - w) ^ (-r) ≤ 1 + 2 * w * ((2:ℝ) ^ r - 1) := by
  have h1w : 0 < 1 - w := by linarith
  -- log(1-w) ≥ -2 log 2 · w
  have hlog : -(2 * Real.log 2 * w) ≤ Real.log (1 - w) := by
    have hc := (strictConcaveOn_log_Ioi.concaveOn).2 (show (1:ℝ) ∈ Ioi 0 by norm_num)
      (show (1/2:ℝ) ∈ Ioi 0 by norm_num) (by linarith : 0 ≤ 1 - 2 * w) (by linarith : 0 ≤ 2 * w)
      (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
    have e : (1 - 2 * w) * 1 + 2 * w * (1 / 2) = 1 - w := by ring
    rw [e, one_div, Real.log_inv] at hc
    linarith
  rw [Real.rpow_def_of_pos h1w]
  have hexp : Real.exp (Real.log (1 - w) * -r) ≤ Real.exp ((2 * w) * (r * Real.log 2)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  refine hexp.trans ?_
  have hc := convexOn_exp.2 (mem_univ 0) (mem_univ (r * Real.log 2)) (by linarith : 0 ≤ 1 - 2 * w)
    (by linarith : 0 ≤ 2 * w) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have h2r : Real.exp (r * Real.log 2) = (2:ℝ) ^ r := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm]
  rw [h2r] at hc
  linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (W : Fin n → Ω → ℝ) (hW_meas : ∀ i, Measurable (W i))
    (hW_range : ∀ i ω, W i ω ∈ Icc (0 : ℝ) (1 / 2))
    (hW_indep : iIndepFun W μ)
    (hW_sum : ∑ i, ∫ ω, W i ω ∂μ ≤ 1 / 2)
    (r : ℝ) (hr : 0 < r) (A : Set Ω) (hA : MeasurableSet A) :
    ∫ ω in A, (∏ i, (1 - W i ω)) ∂μ ≥
      Real.exp (-((2 : ℝ) ^ r) / r) * (μ.real A) ^ (1 + 1 / r) := by
  set f : Ω → ℝ := fun ω => ∏ i, (1 - W i ω) with hf
  have h1W : ∀ i ω, 1 / 2 ≤ 1 - W i ω := fun i ω => by linarith [(hW_range i ω).2]
  have hfpos : ∀ ω, 0 < f ω := fun ω => Finset.prod_pos (fun i _ => by linarith [h1W i ω])
  have hfle : ∀ ω, f ω ≤ 1 := fun ω => Finset.prod_le_one (fun i _ => by linarith [h1W i ω])
    (fun i _ => by linarith [(hW_range i ω).1])
  have hfm : Measurable f := Finset.measurable_prod _ (fun i _ => measurable_const.sub (hW_meas i))
  -- moment bound E f^{-r} ≤ exp(2^r)
  have hmom : ∫ ω, f ω ^ (-r) ∂μ ≤ Real.exp ((2:ℝ) ^ r) := by
    have hprod : ∀ ω, f ω ^ (-r) = ∏ i, (1 - W i ω) ^ (-r) := fun ω => by
      rw [hf, ← Real.finset_prod_rpow _ _ (fun i _ => by linarith [h1W i ω])]
    simp_rw [hprod]
    rw [hW_indep.integral_fun_prod_comp (f := fun _ x => (1 - x) ^ (-r))
      (fun i => (hW_meas i).aemeasurable)
      (fun i => ((measurable_const.sub measurable_id).pow_const (-r)).aestronglyMeasurable)]
    have hWi : ∀ i, Integrable (W i) μ := fun i =>
      Integrable.of_mem_Icc 0 (1/2) (hW_meas i).aemeasurable (Filter.Eventually.of_forall (hW_range i))
    have hone : ∀ i, ∫ ω, (1 - W i ω) ^ (-r) ∂μ ≤ Real.exp (2 * ((2:ℝ) ^ r - 1) * ∫ ω, W i ω ∂μ) := by
      intro i
      have hb : ∀ ω, (1 - W i ω) ^ (-r) ≤ 1 + 2 * W i ω * ((2:ℝ) ^ r - 1) := fun ω =>
        chord_neg_rpow r (W i ω) hr (hW_range i ω).1 (hW_range i ω).2
      have hint1 : Integrable (fun ω => (1 - W i ω) ^ (-r)) μ := by
        refine Integrable.mono' (integrable_const ((1/2:ℝ) ^ (-r)))
          ((measurable_const.sub (hW_meas i)).pow_const (-r)).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun ω => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [h1W i ω]) _)]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) (h1W i ω) (by linarith)
      calc ∫ ω, (1 - W i ω) ^ (-r) ∂μ ≤ ∫ ω, (1 + 2 * W i ω * ((2:ℝ) ^ r - 1)) ∂μ :=
            integral_mono hint1 ((integrable_const 1).add ((hWi i).const_mul 2 |>.mul_const _)) hb
        _ = 1 + 2 * ((2:ℝ) ^ r - 1) * ∫ ω, W i ω ∂μ := by
            rw [integral_add (integrable_const 1) ((hWi i).const_mul 2 |>.mul_const _), integral_const,
              integral_mul_const, integral_const_mul]
            simp; ring
        _ ≤ _ := by linarith [Real.add_one_le_exp (2 * ((2:ℝ) ^ r - 1) * ∫ ω, W i ω ∂μ)]
    calc ∏ i, ∫ ω, (1 - W i ω) ^ (-r) ∂μ
        ≤ ∏ i, Real.exp (2 * ((2:ℝ) ^ r - 1) * ∫ ω, W i ω ∂μ) :=
          Finset.prod_le_prod (fun i _ => integral_nonneg (fun ω =>
            Real.rpow_nonneg (by linarith [h1W i ω]) _)) (fun i _ => hone i)
      _ = Real.exp (2 * ((2:ℝ) ^ r - 1) * ∑ i, ∫ ω, W i ω ∂μ) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp ((2:ℝ) ^ r) := by
          apply Real.exp_le_exp.mpr
          have h2r : (1:ℝ) ≤ (2:ℝ) ^ r := Real.one_le_rpow (by norm_num) hr.le
          nlinarith [integral_nonneg (μ := μ) (f := fun ω => ∑ i, W i ω)
            (fun ω => Finset.sum_nonneg (fun i _ => (hW_range i ω).1))]
  -- Hölder on μ restricted to A
  set a : ℝ := r / (r + 1) with ha
  have ha0 : 0 < a := by positivity
  set pE : ℝ := (r + 1) / r with hpE
  have hp1 : 1 < pE := by rw [hpE, one_lt_div hr]; linarith
  have hpq : pE.HolderConjugate (r + 1) := by
    rw [Real.holderConjugate_iff_eq_conjExponent hp1, hpE]; field_simp; ring
  set F : Ω → ℝ := fun ω => f ω ^ a with hF
  set G : Ω → ℝ := fun ω => f ω ^ (-a) with hG
  have hflow : ∀ ω, (1 / 2 : ℝ) ^ n ≤ f ω := fun ω => by
    calc (1 / 2 : ℝ) ^ n = ∏ _i : Fin n, (1 / 2 : ℝ) := by simp
      _ ≤ f ω := Finset.prod_le_prod (fun i _ => by norm_num) (fun i _ => h1W i ω)
  have hFG : ∀ ω, f ω ^ a * f ω ^ (-a) = 1 := fun ω => by
    rw [← Real.rpow_add (hfpos ω)]; simp
  have hFp : ∀ ω, (f ω ^ a) ^ pE = f ω := fun ω => by
    rw [← Real.rpow_mul (hfpos ω).le, hpE, ha]
    rw [show r / (r + 1) * ((r + 1) / r) = 1 by field_simp, Real.rpow_one]
  have hGq : ∀ ω, (f ω ^ (-a)) ^ (r + 1) = f ω ^ (-r) := fun ω => by
    rw [← Real.rpow_mul (hfpos ω).le, ha]
    congr 1; field_simp
  haveI : IsFiniteMeasure (μ.restrict A) := inferInstance
  have hFm : Measurable F := hfm.pow_const a
  have hGm : Measurable G := hfm.pow_const (-a)
  have hFmem : MemLp F (ENNReal.ofReal pE) (μ.restrict A) := by
    refine MemLp.of_bound hFm.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hfpos ω).le _)]
    exact Real.rpow_le_one (hfpos ω).le (hfle ω) ha0.le
  have hGmem : MemLp G (ENNReal.ofReal (r + 1)) (μ.restrict A) := by
    refine MemLp.of_bound hGm.aestronglyMeasurable (((1 / 2 : ℝ) ^ n) ^ (-a))
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hfpos ω).le _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (hflow ω) (by linarith)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hfpos ω).le _))
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hfpos ω).le _)) hFmem hGmem
  simp_rw [hFG, hFp, hGq] at hH
  rw [integral_const, smul_eq_mul, mul_one] at hH
  rw [measureReal_restrict_apply_univ] at hH
  set I := ∫ ω in A, f ω ∂μ with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg hA (fun ω _ => (hfpos ω).le)
  have hfr_int : Integrable (fun ω => f ω ^ (-r)) μ := by
    refine Integrable.mono' (integrable_const (((1 / 2 : ℝ) ^ n) ^ (-r)))
      (hfm.pow_const (-r)).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hfpos ω).le _)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (hflow ω) (by linarith)
  have hJ : ∫ ω in A, f ω ^ (-r) ∂μ ≤ Real.exp ((2:ℝ) ^ r) :=
    (setIntegral_le_integral hfr_int (Filter.Eventually.of_forall
      (fun ω => Real.rpow_nonneg (hfpos ω).le _))).trans hmom
  have hJ0 : 0 ≤ ∫ ω in A, f ω ^ (-r) ∂μ :=
    setIntegral_nonneg hA (fun ω _ => Real.rpow_nonneg (hfpos ω).le _)
  have hstep : μ.real A ≤ I ^ (1 / pE) * Real.exp ((2:ℝ) ^ r) ^ (1 / (r + 1)) := by
    refine hH.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hI0 _))
    exact Real.rpow_le_rpow hJ0 hJ (by positivity)
  -- raise to the power pE
  have hA0 : 0 ≤ μ.real A := measureReal_nonneg
  have hpow := Real.rpow_le_rpow hA0 hstep (by positivity : (0:ℝ) ≤ pE)
  rw [Real.mul_rpow (Real.rpow_nonneg hI0 _) (Real.rpow_nonneg (Real.exp_pos _).le _),
    ← Real.rpow_mul hI0, ← Real.rpow_mul (Real.exp_pos _).le] at hpow
  rw [show 1 / pE * pE = 1 by field_simp, Real.rpow_one] at hpow
  rw [show 1 / (r + 1) * pE = 1 / r by rw [hpE]; field_simp] at hpow
  rw [← Real.exp_mul] at hpow
  have he : (1 + 1 / r) = pE := by rw [hpE]; field_simp
  rw [ge_iff_le, he]
  have hexpinv : Real.exp (-((2:ℝ) ^ r) / r) * Real.exp ((2:ℝ) ^ r * (1 / r)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc Real.exp (-((2:ℝ) ^ r) / r) * μ.real A ^ pE
      ≤ Real.exp (-((2:ℝ) ^ r) / r) * (I * Real.exp ((2:ℝ) ^ r * (1 / r))) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = I := by rw [mul_comm I, ← mul_assoc, hexpinv, one_mul]
