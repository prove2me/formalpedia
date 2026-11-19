-- Prove2me | solution 1 for ReserveLB.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:26:37.781197+00:00
-- url     : https://prove2.me/submissions/3d3470c3-c864-49ae-93f6-af8972be5b9c

import Mathlib

open MeasureTheory ProbabilityTheory

lemma chord_exp (c z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (-c * z) ≤ 1 - z * (1 - Real.exp (-c)) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-c)) (by linarith : 0 ≤ 1 - z) hz0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc Real.exp (-c * z) = Real.exp (z * -c) := by ring_nf
    _ ≤ (1 - z) + z * Real.exp (-c) := h
    _ = _ := by ring

/-- mgf bound for a [0,1] variable at a nonpositive argument -/
lemma mgf_le_01 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZm : Measurable Z) (hZ01 : ∀ ω, 0 ≤ Z ω ∧ Z ω ≤ 1) (c : ℝ) :
    mgf Z P (-c) ≤ Real.exp (-(1 - Real.exp (-c)) * ∫ ω, Z ω ∂P) := by
  have hZi : Integrable Z P := by
    refine Integrable.mono' (integrable_const 1) hZm.aestronglyMeasurable ?_
    filter_upwards with ω; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hZ01 ω]
  have hEi : Integrable (fun ω => Real.exp (-c * Z ω)) P := by
    refine Integrable.mono' (integrable_const (Real.exp |c|)) (by fun_prop) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := hZ01 ω
    have : |(-c * Z ω)| ≤ |c| := by
      rw [abs_mul, abs_neg, abs_of_nonneg this.1]
      exact mul_le_of_le_one_right (abs_nonneg c) this.2
    linarith [le_abs_self (-c * Z ω)]
  rw [mgf]
  calc ∫ ω, Real.exp (-c * Z ω) ∂P ≤ ∫ ω, (1 - Z ω * (1 - Real.exp (-c))) ∂P :=
        integral_mono hEi ((integrable_const 1).sub (hZi.mul_const _))
          (fun ω => chord_exp c (Z ω) (hZ01 ω).1 (hZ01 ω).2)
    _ = 1 - (∫ ω, Z ω ∂P) * (1 - Real.exp (-c)) := by
        rw [integral_sub (integrable_const 1) (hZi.mul_const _), integral_const, integral_mul_const]
        simp
    _ ≤ Real.exp (-(1 - Real.exp (-c)) * ∫ ω, Z ω ∂P) := by
        have := Real.add_one_le_exp (-(1 - Real.exp (-c)) * ∫ ω, Z ω ∂P)
        linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (Z : Fin n → Ω → ℝ) (hZm : ∀ j, Measurable (Z j)) (hind : iIndepFun Z P)
    (hZ01 : ∀ j ω, 0 ≤ Z j ω ∧ Z j ω ≤ 1) (t : ℝ) (ht : 0 < t)
    (htμ : t ≤ ∫ ω, ∑ j, Z j ω ∂P) :
    P.real {ω | ∑ j, Z j ω ≤ t} ≤
      Real.exp (t * Real.log ((∫ ω, ∑ j, Z j ω ∂P) / t) + t - ∫ ω, ∑ j, Z j ω ∂P) := by
  set M := ∫ ω, ∑ j, Z j ω ∂P with hM
  have hM0 : 0 < M := lt_of_lt_of_le ht htμ
  have hZi : ∀ j, Integrable (Z j) P := by
    intro j
    refine Integrable.mono' (integrable_const 1) (hZm j).aestronglyMeasurable ?_
    filter_upwards with ω; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hZ01 j ω]
  have hMsum : M = ∑ j, ∫ ω, Z j ω ∂P := by
    rw [hM, integral_finset_sum _ (fun j _ => hZi j)]
  set c := Real.log (M / t) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hec : Real.exp (-c) = t / M := by
    rw [hc, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  set S : Ω → ℝ := ∑ j, Z j with hS
  have hSfun : ∀ ω, S ω = ∑ j, Z j ω := fun ω => by simp [hS]
  have hSm : Measurable S := by
    have : S = fun ω => ∑ j, Z j ω := funext hSfun
    rw [this]; fun_prop
  have hSint : Integrable (fun ω => Real.exp (-c * S ω)) P := by
    refine Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : 0 ≤ S ω := by rw [hSfun]; exact Finset.sum_nonneg (fun j _ => (hZ01 j ω).1)
    nlinarith
  have hCh := measure_le_le_exp_mul_mgf (μ := P) (X := S) t (neg_nonpos.mpr hc0) hSint
  have hset : {ω | ∑ j, Z j ω ≤ t} = {ω | S ω ≤ t} := by ext ω; simp [hSfun]
  rw [hset]
  refine hCh.trans ?_
  rw [hS, hind.mgf_sum hZm]
  have hprod : ∏ j ∈ Finset.univ, mgf (Z j) P (-c) ≤
      ∏ j ∈ Finset.univ, Real.exp (-(1 - Real.exp (-c)) * ∫ ω, Z j ω ∂P) :=
    Finset.prod_le_prod (fun j _ => mgf_nonneg) (fun j _ => mgf_le_01 P (Z j) (hZm j) (hZ01 j) c)
  rw [← Real.exp_sum, ← Finset.mul_sum, ← hMsum, hec] at hprod
  calc Real.exp (- -c * t) * ∏ j ∈ Finset.univ, mgf (Z j) P (-c)
      ≤ Real.exp (- -c * t) * Real.exp (-(1 - t / M) * M) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_add]; congr 1; rw [hc]; field_simp; ring
