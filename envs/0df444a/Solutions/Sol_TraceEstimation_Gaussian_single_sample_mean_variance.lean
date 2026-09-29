-- Prove2me | solution 1 for TraceEstimation.Gaussian.single_sample_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:07:04.845641+00:00
-- url     : https://prove2.me/submissions/eeae1a75-3518-4c5f-ad79-d69db1928525

import Mathlib
import Definitions.Def_TraceEstimation_Shared_gaussianEstimator

namespace TraceEstimation.Gaussian

open MeasureTheory ProbabilityTheory Matrix

lemma aux_sm_e_hasDeriv (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t := by
  have h := ((hasDerivAt_pow 2 t).div_const 2).exp
  convert h using 1
  norm_num
  ring

lemma aux_sm_mom (k : ℕ) :
    ∫ t, t ^ k ∂(gaussianReal 0 1) = iteratedDeriv k (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := (id : ℝ → ℝ)) (μ := gaussianReal 0 1) (by simp) k
  rw [mgf_id_gaussianReal] at h
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul] at h
  rw [h]
  rfl

lemma aux_sm_d1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t => t * Real.exp (t ^ 2 / 2) := by
  funext t
  exact (aux_sm_e_hasDeriv t).deriv

lemma aux_sm_d2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
    fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
  funext t
  have h : HasDerivAt (fun t : ℝ => t * Real.exp (t ^ 2 / 2))
      (1 * Real.exp (t ^ 2 / 2) + id t * (t * Real.exp (t ^ 2 / 2))) t :=
    (hasDerivAt_id t).mul (aux_sm_e_hasDeriv t)
  rw [h.deriv]
  simp only [id]
  ring

lemma aux_sm_d3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
    fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
  funext t
  have h : HasDerivAt (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2))
      (((2 : ℕ) * t ^ (2 - 1)) * Real.exp (t ^ 2 / 2) + (1 + t ^ 2) * (t * Real.exp (t ^ 2 / 2))) t :=
    ((hasDerivAt_pow 2 t).const_add 1).mul (aux_sm_e_hasDeriv t)
  rw [h.deriv]
  norm_num
  ring

lemma aux_sm_d4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
    fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
  funext t
  have h : HasDerivAt (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2))
      ((3 * 1 + (3 : ℕ) * t ^ (3 - 1)) * Real.exp (t ^ 2 / 2) +
        (3 * t + t ^ 3) * (t * Real.exp (t ^ 2 / 2))) t :=
    (((hasDerivAt_id t).const_mul 3).add (hasDerivAt_pow 3 t)).mul (aux_sm_e_hasDeriv t)
  rw [h.deriv]
  norm_num
  ring

lemma aux_sm_m2 : ∫ t, t ^ 2 ∂(gaussianReal 0 1) = 1 := by
  rw [aux_sm_mom, iteratedDeriv_succ, iteratedDeriv_one, aux_sm_d1, aux_sm_d2]
  simp

lemma aux_sm_m4 : ∫ t, t ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [aux_sm_mom, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    aux_sm_d1, aux_sm_d2, aux_sm_d3, aux_sm_d4]
  simp

lemma aux_sm_E2 {n : ℕ} (j : Fin n) :
    ∫ x, x j ^ 2 ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1 := by
  exact (integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1) (i := j)
    (f := fun t : ℝ => t ^ 2) (continuous_pow 2).aestronglyMeasurable).trans aux_sm_m2

lemma aux_sm_E4 {n : ℕ} (j : Fin n) :
    ∫ x, x j ^ 4 ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 3 := by
  exact (integral_comp_eval (μ := fun _ : Fin n => gaussianReal 0 1) (i := j)
    (f := fun t : ℝ => t ^ 4) (continuous_pow 4).aestronglyMeasurable).trans aux_sm_m4

lemma aux_sm_E22 {n : ℕ} (j l : Fin n) (h : j ≠ l) :
    ∫ x, x j ^ 2 * x l ^ 2 ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1 := by
  have hind := iIndepFun_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun h).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have h3 := h2.integral_fun_mul_eq_mul_integral
    (Continuous.aestronglyMeasurable (by fun_prop)) (Continuous.aestronglyMeasurable (by fun_prop))
  simp only [Function.comp_apply, id] at h3
  rw [h3]
  rw [aux_sm_E2, aux_sm_E2, one_mul]

lemma aux_sm_odd {n : ℕ} (p : Fin n) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F)
    (hR : ∀ x, F (fun i => if i = p then -x i else x i) = -F x) :
    ∫ x, F x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 0 := by
  have hmp : MeasurePreserving (fun (x : Fin n → ℝ) (i : Fin n) => if i = p then -x i else x i)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    refine measurePreserving_pi (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
      (f := fun i t => if i = p then -t else t) (fun i => ?_)
    by_cases hi : i = p
    · simp only [hi, if_true]
      refine ⟨measurable_neg, ?_⟩
      rw [gaussianReal_map_neg, neg_zero]
    · simp only [hi, if_false]
      exact MeasurePreserving.id _
  have key : ∫ x, F x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∫ x, F (fun i => if i = p then -x i else x i)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    conv_lhs => rw [← hmp.map_eq]
    rw [integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable]
  simp only [hR, integral_neg] at key
  linarith

lemma aux_sm_E11 {n : ℕ} (j k : Fin n) :
    ∫ x, x j * x k ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      if j = k then 1 else 0 := by
  by_cases h : j = k
  · subst h
    rw [if_pos rfl, ← aux_sm_E2 j]
    congr 1
    funext x
    ring
  · rw [if_neg h]
    exact aux_sm_odd j _ (by fun_prop) (fun x => by simp [Ne.symm h])

lemma aux_sm_M {n : ℕ} (j k l m : Fin n) :
    ∫ x, x j * x k * x l * x m ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      (if j = k then 1 else 0) * (if l = m then 1 else 0) +
      (if j = l then 1 else 0) * (if k = m then 1 else 0) +
      (if j = m then 1 else 0) * (if k = l then 1 else 0) := by
  by_cases hjk : j = k
  · subst hjk
    by_cases hjl : j = l
    · subst hjl
      by_cases hjm : j = m
      · subst hjm
        simp only [if_true, mul_one]
        rw [show (1:ℝ) + 1 + 1 = 3 by norm_num, ← aux_sm_E4 j]
        congr 1
        funext x
        ring
      · rw [aux_sm_odd m _ (by fun_prop) (fun x => by simp [hjm, Ne.symm hjm])]
        simp [hjm, Ne.symm hjm]
    · by_cases hjm : j = m
      · subst hjm
        rw [aux_sm_odd l _ (by fun_prop) (fun x => by simp [hjl, Ne.symm hjl])]
        simp [hjl, Ne.symm hjl]
      · by_cases hlm : l = m
        · subst hlm
          simp [hjl, Ne.symm hjl]
          rw [← aux_sm_E22 j l hjl]
          congr 1
          funext x
          ring
        · rw [aux_sm_odd l _ (by fun_prop) (fun x => by simp [hjl, Ne.symm hlm])]
          simp [hjl, Ne.symm hjl, hlm]
  · by_cases hjl : j = l
    · subst hjl
      by_cases hjm : j = m
      · subst hjm
        rw [aux_sm_odd k _ (by fun_prop) (fun x => by simp [hjk, Ne.symm hjk])]
        simp [hjk, Ne.symm hjk]
      · by_cases hkm : k = m
        · subst hkm
          simp [hjk, Ne.symm hjk]
          rw [← aux_sm_E22 j k hjk]
          congr 1
          funext x
          ring
        · rw [aux_sm_odd k _ (by fun_prop) (fun x => by simp [hjk, Ne.symm hkm])]
          simp [hjk, Ne.symm hjk, hkm]
    · by_cases hjm : j = m
      · subst hjm
        by_cases hkl : k = l
        · subst hkl
          simp [hjk, Ne.symm hjk]
          rw [← aux_sm_E22 j k hjk]
          congr 1
          funext x
          ring
        · rw [aux_sm_odd k _ (by fun_prop) (fun x => by simp [hjk, Ne.symm hkl])]
          simp [hjk, Ne.symm hjk, hkl]
      · rw [aux_sm_odd j _ (by fun_prop) (fun x => by simp [hjk, hjl, hjm, Ne.symm hjk,
          Ne.symm hjl, Ne.symm hjm])]
        simp [hjk, hjl, hjm]

lemma aux_sm_x4 {n : ℕ} (j : Fin n) :
    MemLp (fun x : Fin n → ℝ => x j) 4 (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
  (memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by simp)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j)

lemma aux_sm_holder : ENNReal.HolderTriple 4 4 2 := by
  refine ⟨?_⟩
  rw [← two_mul]
  have h4 : (4 : ENNReal) = 2 * 2 := by norm_num
  rw [h4, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

lemma aux_sm_xx {n : ℕ} (j k : Fin n) :
    MemLp (fun x : Fin n → ℝ => x j * x k) 2 (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have := aux_sm_holder
  exact (aux_sm_x4 k).mul' (aux_sm_x4 j)

lemma aux_sm_Q_memLp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x : Fin n → ℝ => ∑ j, ∑ k, A j k * (x j * x k)) 2
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
  memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun k _ => (aux_sm_xx j k).const_mul (A j k)

lemma aux_sm_Q_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, ∑ j, ∑ k, A j k * (x j * x k) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      A.trace := by
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ =>
    ((aux_sm_xx j k).const_mul (A j k)).integrable one_le_two)]
  simp_rw [integral_finsetSum _ (fun k _ =>
    ((aux_sm_xx _ k).const_mul (A _ k)).integrable one_le_two)]
  simp_rw [integral_const_mul, aux_sm_E11]
  simp [Matrix.trace]

lemma aux_sm_Q_sq_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, (∑ j, ∑ k, A j k * (x j * x k)) ^ 2 ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∑ j, ∑ k, ∑ l, ∑ m, A j k * A l m *
        ((if j = k then 1 else 0) * (if l = m then 1 else 0) +
          (if j = l then 1 else 0) * (if k = m then 1 else 0) +
          (if j = m then 1 else 0) * (if k = l then 1 else 0)) := by
  have : ENNReal.HolderTriple 2 2 1 := inferInstance
  have hint : ∀ j k l m : Fin n, Integrable (fun x : Fin n → ℝ =>
      A j k * (x j * x k) * (A l m * (x l * x m))) (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    fun j k l m => memLp_one_iff_integrable.mp
      (((aux_sm_xx l m).const_mul (A l m)).mul' ((aux_sm_xx j k).const_mul (A j k)))
  have hexp : ∀ x : Fin n → ℝ, (∑ j, ∑ k, A j k * (x j * x k)) ^ 2 =
      ∑ j, ∑ k, ∑ l, ∑ m, A j k * (x j * x k) * (A l m * (x l * x m)) := by
    intro x
    rw [sq]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ => hint j k l m)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ =>
    integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ => hint j k l m)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ fun m _ => hint j k l m)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ (fun m _ => hint j k l m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← aux_sm_M, ← integral_const_mul]
  congr 1
  funext x
  ring

lemma aux_sm_final {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, A j i = A i j) :
    (∑ j, ∑ k, ∑ l, ∑ m, A j k * A l m *
        ((if j = k then 1 else 0) * (if l = m then 1 else 0) +
          (if j = l then 1 else 0) * (if k = m then 1 else 0) +
          (if j = m then 1 else 0) * (if k = l then 1 else 0))) - A.trace ^ 2 =
      2 * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 := by
  simp [mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.sum_ite_irrel, Matrix.trace]
  have h1 : ∑ x : Fin n, ∑ y : Fin n, A x x * A y y = (∑ i, A i i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : ∑ x : Fin n, ∑ y : Fin n, A x y * A x y = ∑ x : Fin n, ∑ y : Fin n, A x y ^ 2 := by
    simp [sq]
  have h3 : ∑ x : Fin n, ∑ y : Fin n, A x y * A y x = ∑ x : Fin n, ∑ y : Fin n, A x y ^ 2 :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hA x y, sq]
  rw [h1, h2, h3]
  ring

end TraceEstimation.Gaussian

open TraceEstimation TraceEstimation.Gaussian
open MeasureTheory ProbabilityTheory Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    MemLp (Shared.gaussianEstimator A 1) 2 (Shared.gaussianSampleMeasure n 1) ∧
    ∫ ω, Shared.gaussianEstimator A 1 ω ∂(Shared.gaussianSampleMeasure n 1) = A.trace ∧
    variance (Shared.gaussianEstimator A 1) (Shared.gaussianSampleMeasure n 1) =
      2 * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 := by
  have hG : Shared.gaussianEstimator A 1 = fun ω =>
      (fun x : Fin n → ℝ => ∑ j, ∑ k, A j k * (x j * x k))
        (MeasurableEquiv.funUnique (Fin 1) (Fin n → ℝ) ω) := by
    funext ω
    simp only [Shared.gaussianEstimator, dotProduct, mulVec, Finset.univ_unique,
      Finset.sum_singleton, Nat.cast_one, inv_one, one_mul, Finset.mul_sum]
    show _ = ∑ j, ∑ k, A j k * (ω default j * ω default k)
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have he : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) (Fin n → ℝ))
      (Shared.gaussianSampleMeasure n 1) (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    measurePreserving_funUnique _ _
  have hsym : ∀ i j, A j i = A i j := fun i j => by simpa using hA.apply i j
  refine ⟨?_, ?_, ?_⟩
  · rw [hG]
    exact (aux_sm_Q_memLp A).comp_measurePreserving he
  · rw [hG, he.integral_comp' (fun x : Fin n → ℝ => ∑ j, ∑ k, A j k * (x j * x k))]
    exact aux_sm_Q_int A
  · rw [hG, he.variance_fun_comp (aux_sm_Q_memLp A).aemeasurable,
      variance_eq_sub (aux_sm_Q_memLp A), aux_sm_Q_int]
    simp only [Pi.pow_apply]
    rw [aux_sm_Q_sq_int]
    exact aux_sm_final A hsym
