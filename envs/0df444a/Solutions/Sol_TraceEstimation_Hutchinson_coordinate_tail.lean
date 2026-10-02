-- Prove2me | solution 1 for TraceEstimation.Hutchinson.coordinate_tail
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T20:29:12.737031+00:00
-- url     : https://prove2.me/submissions/07a8924c-19a7-4b03-a54c-fee28c06b47e

import Mathlib
import Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Hutchinson

namespace HutchinsonProof

lemma integrable_rademacher (f : ℝ → ℝ) : Integrable f rademacher := by
  unfold rademacher
  exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
    (by simp)

lemma integral_rademacher (f : ℝ → ℝ) :
    (∫ x, f x ∂rademacher) = (f 1 + f (-1)) / 2 := by
  unfold rademacher
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp))]
  simp [integral_dirac, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

lemma rademacher_ae_sign : ∀ᵐ x : ℝ ∂rademacher, x = 1 ∨ x = -1 := by
  simp [rademacher, ae_add_measure_iff]

lemma pi_ae_sign {ι : Type*} [Fintype ι] :
    ∀ᵐ x : ι → ℝ ∂Measure.pi (fun _ : ι => rademacher), ∀ i, x i = 1 ∨ x i = -1 := by
  exact Filter.eventually_all.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => rademacher) (i := i)).eventually
      rademacher_ae_sign)

lemma integrable_pi_continuous {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ)
    (hf : Continuous f) : Integrable f (Measure.pi (fun _ : ι => rademacher)) := by
  let K : Set (ι → ℝ) := Set.Icc (fun _ => -1) (fun _ => 1)
  have hK : IsCompact K := isCompact_Icc
  have ha : ∀ᵐ x : ι → ℝ ∂Measure.pi (fun _ : ι => rademacher), x ∈ K := by
    filter_upwards [pi_ae_sign] with x hx
    constructor <;> intro i <;> rcases hx i with h | h <;> simp [h]
  have hi := hf.continuousOn.integrableOn_compact (μ := Measure.pi (fun _ : ι => rademacher)) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi

lemma rademacher_linear_mgf {ι : Type*} [Fintype ι] (a : ι → ℝ) (s : ℝ) :
    (∫ x : ι → ℝ, exp (s * ∑ i, a i * x i)
      ∂Measure.pi (fun _ : ι => rademacher)) ≤ exp (s ^ 2 / 2 * ∑ i, a i ^ 2) := by
  classical
  have hr : ∀ x : ι → ℝ, s * ∑ i, a i * x i = ∑ i, (s * a i) * x i := by
    intro x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hr, exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => exp ((s * a i) * x))]
  have hc : ∀ i, (∫ x : ℝ, exp ((s * a i) * x) ∂rademacher) ≤ exp ((s * a i) ^ 2 / 2) := by
    intro i
    rw [integral_rademacher]
    simpa only [mul_one, mul_neg_one, ← cosh_eq] using cosh_le_exp_half_sq (s * a i)
  calc
    (∏ i, ∫ x : ℝ, exp ((s * a i) * x) ∂rademacher) ≤ ∏ i, exp ((s * a i) ^ 2 / 2) :=
      Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (exp_pos _).le)) (fun i _ => hc i)
    _ = exp (s ^ 2 / 2 * ∑ i, a i ^ 2) := by
      rw [← exp_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

end HutchinsonProof


section

open MeasureTheory ProbabilityTheory Matrix Finset
namespace CTraceHutch
open TraceEstimation.Hutchinson

instance vec_prob (n : ℕ) : IsProbabilityMeasure (rademacherVectorMeasure n) := by
  unfold rademacherVectorMeasure
  infer_instance

theorem sign_square (n : ℕ) : ∀ᵐ z ∂rademacherVectorMeasure n,∀ i,z i^2=1 := by
  rw [ae_all_iff]
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin n=>rademacher) i).ae
    (show ∀ᵐ x ∂rademacher,x^2=1 by simp [rademacher,ae_add_measure_iff])

theorem sign_abs (n : ℕ) : ∀ᵐ z ∂rademacherVectorMeasure n,∀ i,|z i|=1 := by
  filter_upwards [sign_square n] with z hz i
  have h:=hz i
  have ha:=sq_abs (z i)
  have hb:=abs_nonneg (z i)
  nlinarith

theorem sign_mean : (∫ x,x ∂rademacher)=0 := by
  rw [rademacher,integral_smul_measure,integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp))]
  simp

theorem character_mean {n : ℕ} (s : Finset (Fin n)) :
    (∫ z,∏ i∈s,z i ∂rademacherVectorMeasure n)=if s=∅ then 1 else 0 := by
  classical
  have hprod (z : Fin n → ℝ) : (∏ i∈s,z i)=∏ i : Fin n,if i∈s then z i else 1 := by simp
  simp_rw [hprod]
  rw [rademacherVectorMeasure,integral_fintype_prod_eq_prod (fun i (x : ℝ)=>if i∈s then x else 1)]
  by_cases hs : s=∅
  · simp [hs]
  · rw [if_neg hs]
    obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr hs
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa [hi] using sign_mean

theorem pair_memLp {n : ℕ} (i j : Fin n) (p : ENNReal) :
    MemLp (fun z : Fin n → ℝ=>z i*z j) p (rademacherVectorMeasure n) := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [sign_abs n] with z hz
  simp [Real.norm_eq_abs,abs_mul,hz]

theorem pair_mean {n : ℕ} (i j : Fin n) :
    (∫ z,z i*z j ∂rademacherVectorMeasure n)=if i=j then 1 else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    calc
      _=∫ _ : Fin n → ℝ,(1 : ℝ) ∂rademacherVectorMeasure n := by
        apply integral_congr_ae
        filter_upwards [sign_square n] with z hz
        simpa [pow_two] using hz i
      _=1 := by simp
  · simpa [hij] using character_mean ({i,j} : Finset (Fin n))

theorem four_mean {n : ℕ} (i j k l : Fin n) (hij : i≠j) (hkl : k≠l) :
    (∫ z,(z i*z j)*(z k*z l) ∂rademacherVectorMeasure n)=
      (if i=k ∧ j=l then (1 : ℝ) else 0)+(if i=l ∧ j=k then 1 else 0) := by
  classical
  have hsq := sign_square n
  by_cases hik : i=k
  · subst k
    have he : (∫ z,(z i*z j)*(z i*z l) ∂rademacherVectorMeasure n)=∫ z,z j*z l ∂rademacherVectorMeasure n := by
      apply integral_congr_ae
      filter_upwards [hsq] with z hz
      calc
        _=z i^2*(z j*z l) := by ring
        _=z j*z l := by rw [hz i,one_mul]
    rw [he,pair_mean]
    simp [hij,Ne.symm hij]
  by_cases hil : i=l
  · subst l
    have he : (∫ z,(z i*z j)*(z k*z i) ∂rademacherVectorMeasure n)=∫ z,z j*z k ∂rademacherVectorMeasure n := by
      apply integral_congr_ae
      filter_upwards [hsq] with z hz
      calc
        _=z i^2*(z j*z k) := by ring
        _=z j*z k := by rw [hz i,one_mul]
    rw [he,pair_mean]
    simp [hik]
  by_cases hjk : j=k
  · subst k
    have he : (∫ z,(z i*z j)*(z j*z l) ∂rademacherVectorMeasure n)=∫ z,z i*z l ∂rademacherVectorMeasure n := by
      apply integral_congr_ae
      filter_upwards [hsq] with z hz
      calc
        _=z j^2*(z i*z l) := by ring
        _=z i*z l := by rw [hz j,one_mul]
    rw [he,pair_mean]
    simp [hij,hil]
  by_cases hjl : j=l
  · subst l
    have he : (∫ z,(z i*z j)*(z k*z j) ∂rademacherVectorMeasure n)=∫ z,z i*z k ∂rademacherVectorMeasure n := by
      apply integral_congr_ae
      filter_upwards [hsq] with z hz
      calc
        _=z j^2*(z i*z k) := by ring
        _=z i*z k := by rw [hz j,one_mul]
    rw [he,pair_mean]
    simp [hij,hik]
  · have h:=character_mean ({i,j,k,l} : Finset (Fin n))
    simpa [hij,hik,hil,hjk,hjl,hkl,mul_assoc] using h

end CTraceHutch
end

section

open MeasureTheory ProbabilityTheory Matrix Finset
namespace CTraceHutch
open TraceEstimation.Hutchinson

theorem pair_covariance {n : ℕ} (i j k l : Fin n) :
    covariance (fun z : Fin n → ℝ=>z i*z j) (fun z=>z k*z l) (rademacherVectorMeasure n)=
      if i=j then 0 else
        (if i=k ∧ j=l then (1 : ℝ) else 0)+(if i=l ∧ j=k then 1 else 0) := by
  classical
  by_cases hij : i=j
  · subst j
    simp only [if_pos rfl]
    unfold covariance
    rw [pair_mean]
    simp only [if_pos rfl]
    apply integral_eq_zero_of_ae
    filter_upwards [sign_square n] with z hz
    simp [←pow_two,hz]
  by_cases hkl : k=l
  · subst l
    have hr : (if i=k ∧ j=k then (1 : ℝ) else 0)=0 := by
      split_ifs with h
      · exact False.elim (hij (h.1.trans h.2.symm))
      · rfl
    rw [if_neg hij,hr,zero_add]
    unfold covariance
    rw [pair_mean k k]
    simp only [if_pos rfl]
    apply integral_eq_zero_of_ae
    filter_upwards [sign_square n] with z hz
    simp [←pow_two,hz]
  rw [if_neg hij,covariance_eq_sub (pair_memLp i j 2) (pair_memLp k l 2)]
  change (∫ z,(z i*z j)*(z k*z l) ∂rademacherVectorMeasure n) -
    (∫ z,z i*z j ∂rademacherVectorMeasure n)*(∫ z,z k*z l ∂rademacherVectorMeasure n)=_
  rw [pair_mean,pair_mean,if_neg hij,if_neg hkl,zero_mul,sub_zero,four_mean i j k l hij hkl]

theorem quadratic_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    z ⬝ᵥ (A*ᵥ z)=∑ p : Fin n × Fin n,A p.1 p.2*(z p.1*z p.2) := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem quadratic_memLp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun z=>z ⬝ᵥ (A*ᵥ z)) 2 (rademacherVectorMeasure n) := by
  simp_rw [quadratic_eq]
  have hh:=memLp_finsetSum' Finset.univ (fun (p : Fin n × Fin n) _=>(pair_memLp p.1 p.2 2).const_mul (A p.1 p.2))
  apply MemLp.ae_eq (hf_Lp:=hh)
  exact Filter.Eventually.of_forall (fun z=>by simp)

theorem quadratic_mean {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∫ z,z ⬝ᵥ (A*ᵥ z) ∂rademacherVectorMeasure n)=A.trace := by
  classical
  simp_rw [quadratic_eq]
  rw [integral_finset_sum _ (fun (p : Fin n × Fin n) _=>(pair_memLp p.1 p.2 2).const_mul (A p.1 p.2) |>.integrable (by norm_num))]
  simp_rw [integral_const_mul,pair_mean]
  simp [Fintype.sum_prod_type,Matrix.trace]

theorem quadratic_variance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    variance (fun z=>z ⬝ᵥ (A*ᵥ z)) (rademacherVectorMeasure n)=
      2*(∑ i,∑ j,A i j^2-∑ i,A i i^2) := by
  classical
  simp_rw [quadratic_eq]
  rw [variance_fun_sum (fun (p : Fin n × Fin n)=>(pair_memLp p.1 p.2 2).const_mul (A p.1 p.2))]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right,pair_covariance]
  simp only [Fintype.sum_prod_type]
  have hinner (i j : Fin n) :
      (∑ k : Fin n,∑ l : Fin n,A i j*(A k l*(if i=j then 0 else
        (if i=k ∧ j=l then (1 : ℝ) else 0)+(if i=l ∧ j=k then 1 else 0))))=
        if i=j then 0 else 2*A i j^2 := by
    by_cases hij : i=j
    · simp [hij]
    · simp only [if_neg hij,mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero]
      simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.sum_ite_eq']
      have hsym : A j i=A i j := hA.apply i j
      rw [hsym]
      ring
  simp_rw [hinner]
  have hrow (i : Fin n) : (∑ j,if i=j then (0 : ℝ) else 2*A i j^2)=
      (∑ j,2*A i j^2)-2*A i i^2 := by
    calc
      _=∑ j,(2*A i j^2-(if i=j then 2*A i j^2 else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : i=j <;> simp [h]
      _=_ := by simp [Finset.sum_sub_distrib]
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib]
  simp_rw [←Finset.mul_sum]
  ring

end CTraceHutch
end

section
open MeasureTheory ProbabilityTheory Matrix TraceEstimation.Hutchinson
theorem hutchinson_reference_mean_variance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (MemLp (fun z : Fin n → ℝ => z ⬝ᵥ (A *ᵥ z)) 2 (rademacherVectorMeasure n) ∧
      ∫ z, z ⬝ᵥ (A *ᵥ z) ∂(rademacherVectorMeasure n) = A.trace) ∧
    (A.IsSymm →
      variance (fun z : Fin n → ℝ => z ⬝ᵥ (A *ᵥ z)) (rademacherVectorMeasure n) =
        2 * (∑ i, ∑ j, A i j ^ 2 - ∑ i, A i i ^ 2)) := by
  exact ⟨⟨CTraceHutch.quadratic_memLp A,CTraceHutch.quadratic_mean A⟩,CTraceHutch.quadratic_variance A⟩
end


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Hutchinson

namespace HutchinsonProof

lemma projection_moments {n : ℕ} (α : Fin n → ℝ) (hα : α ⬝ᵥ α = 1) :
    (∫ z, (α ⬝ᵥ z) ^ 2 ∂rademacherVectorMeasure n) = 1 ∧
    (∫ z, (α ⬝ᵥ z) ^ 4 ∂rademacherVectorMeasure n) ≤ 3 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := vecMulVec α α
  have hs : A.IsSymm := by
    rw [IsSymm.ext_iff]
    intro i j
    simp [A, vecMulVec_apply, mul_comm]
  have hsum : ∑ i, α i ^ 2 = 1 := by simpa [dotProduct, pow_two] using hα
  have htr : A.trace = 1 := by simpa [A, trace, vecMulVec_apply, dotProduct, pow_two] using hα
  have hq : ∀ z : Fin n → ℝ, z ⬝ᵥ (A *ᵥ z) = (α ⬝ᵥ z) ^ 2 := by
    intro z
    dsimp [A]
    simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_mul,
      mul_assoc, mul_comm, mul_left_comm, pow_two]
  have hf : (∑ i, ∑ j, A i j ^ 2) = 1 := by
    simp only [A, vecMulVec_apply, mul_pow, ← Finset.mul_sum]
    rw [← Finset.sum_mul, hsum]
    norm_num
  have hm := CTraceHutch.quadratic_mean A
  have hv := CTraceHutch.quadratic_variance A hs
  have hi := CTraceHutch.quadratic_memLp A
  have he := variance_eq_sub hi
  simp only [hq, htr] at hm
  rw [hf] at hv
  simp only [hq] at hv
  simp only [Pi.pow_apply, hq, ← pow_mul, hm] at he
  have hn : 0 ≤ ∑ i, A i i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  exact ⟨hm, by nlinarith [hv, he]⟩

end HutchinsonProof


open Real Set

namespace HutchinsonProof

lemma log_one_add_cubic (x : ℝ) (hx : 0 ≤ x) :
    log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let F := fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3 - log (1 + y)
  let D := fun y : ℝ => 1 - y + y ^ 2 - 1 / (1 + y)
  have hd : ∀ y ∈ Icc 0 x, HasDerivAt F (D y) y := by
    intro y hy
    have hp : 1 + y ≠ 0 := by linarith [hy.1]
    convert (((hasDerivAt_id y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
      ((hasDerivAt_pow 3 y).div_const 3)).sub
        (((hasDerivAt_const y 1).add (hasDerivAt_id y)).log hp) using 1 <;>
      first | rfl | (dsimp [F, D]; ring)
  have hm : MonotoneOn F (Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    have hp : 0 < 1 + y := by linarith
    dsimp [D]
    rw [sub_nonneg]
    apply (div_le_iff₀ hp).mpr
    nlinarith [pow_nonneg hy0 3]
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [F] using hh

lemma lower_poly_pos (h : ℝ) : 0 < 1 - h + 3 / 2 * h ^ 2 := by
  nlinarith [sq_nonneg (h - 1 / 3)]

lemma log_lower_poly (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1 / 2) :
    log (1 - h + 3 / 2 * h ^ 2) ≤ -h + h ^ 2 + 4 / 3 * h ^ 3 := by
  let p := fun y : ℝ => 1 - y + 3 / 2 * y ^ 2
  let F := fun y : ℝ => -y + y ^ 2 + 4 / 3 * y ^ 3 - log (p y)
  let D := fun y : ℝ => -1 + 2 * y + 4 * y ^ 2 - (-1 + 3 * y) / p y
  have hd : ∀ y ∈ Icc 0 h, HasDerivAt F (D y) y := by
    intro y hy
    have hp := ((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      ((hasDerivAt_pow 2 y).const_mul (3 / 2))
    convert ((((hasDerivAt_id y).neg.add (hasDerivAt_pow 2 y)).add
      ((hasDerivAt_pow 3 y).const_mul (4 / 3))).sub
        (hp.log (lower_poly_pos y).ne')) using 1 <;> first | rfl | (dsimp [F, D, p]; ring)
  have hm : MonotoneOn F (Icc 0 h) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 h)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    have hy1 : y ≤ 1 / 2 := (interior_subset hy).2.trans h1
    have hp : 0 < p y := lower_poly_pos y
    dsimp [D]
    rw [sub_nonneg]
    apply (div_le_iff₀ hp).mpr
    dsimp [p]
    nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ 1 / 2 - y by linarith), sq_nonneg (y ^ 2)]
  have hh := hm ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
  simpa [F, p] using hh

lemma lower_parameter_cost (ε : ℝ) (hε : 0 ≤ ε) :
    let h := ε / (2 * (1 + ε));
    -ε * h + h ^ 2 + 4 / 3 * h ^ 3 ≤ -(ε ^ 2 / 4 - ε ^ 3 / 6) := by
  dsimp
  have hp : 0 < 1 + ε := by linarith
  have he : -(ε ^ 2 / 4 - ε ^ 3 / 6) -
      (-ε * (ε / (2 * (1 + ε))) + (ε / (2 * (1 + ε))) ^ 2 +
        4 / 3 * (ε / (2 * (1 + ε))) ^ 3) =
      ε ^ 4 * (3 + 3 * ε + 2 * ε ^ 2) / (12 * (1 + ε) ^ 3) := by
    field_simp [hp.ne']
    ring
  rw [← sub_nonneg, he]
  positivity

lemma exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) : exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let F := fun y : ℝ => 1 - y + y ^ 2 / 2 - exp (-y)
  let D := fun y : ℝ => -1 + y + exp (-y)
  have hd : ∀ y ∈ Icc 0 x, HasDerivAt F (D y) y := by
    intro y hy
    convert (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      ((hasDerivAt_pow 2 y).div_const 2)).sub ((hasDerivAt_id y).neg.exp) using 1 <;>
      first | rfl | (dsimp [F, D]; ring)
  have hm : MonotoneOn F (Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    dsimp [D]
    linarith [add_one_le_exp (-y)]
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [F] using hh

end HutchinsonProof


open MeasureTheory ProbabilityTheory Real

namespace TraceGaussianProof

lemma gaussian_sq_mgf (a : ℝ) (ha : 2 * a < 1) :
    Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) ∧
      (∫ x : ℝ, exp (a * x ^ 2) ∂gaussianReal 0 1) =
        (1 - 2 * a) ^ (-(1 : ℝ) / 2) := by
  have hb : 0 < 1 / 2 - a := by linarith
  have hd : 0 < 1 - 2 * a := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : ∀ x : ℝ, gaussianPDFReal 0 1 x * exp (a * x ^ 2) =
      (sqrt (2 * Real.pi))⁻¹ * exp (-(1 / 2 - a) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  have hwi : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * exp (a * x ^ 2)) := by
    simp_rw [hw]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  have hi : Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hwi
  refine ⟨hi, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
  simp_rw [smul_eq_mul, hw]
  rw [integral_const_mul, integral_gaussian]
  set R := (sqrt (2 * Real.pi))⁻¹ * sqrt (Real.pi / (1 / 2 - a))
  have hR : 0 ≤ R := by positivity
  have hsq : R ^ 2 * (1 - 2 * a) = 1 := by
    dsimp [R]
    rw [mul_pow, inv_pow, sq_sqrt hp.le, sq_sqrt (by positivity)]
    field_simp
  have hs : ((1 - 2 * a) ^ (-(1 : ℝ) / 2)) ^ 2 * (1 - 2 * a) = 1 := by
    rw [← rpow_natCast, ← rpow_mul hd.le]
    norm_num
    rw [rpow_neg_one, inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ hR (rpow_nonneg hd.le _)).mp
  nlinarith

lemma gaussian_pi_sq_mgf {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 2 * d i < 1) :
    Integrable (fun x : ι → ℝ => exp (∑ i, d i * x i ^ 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) ∧
    (∫ x : ι → ℝ, exp (∑ i, d i * x i ^ 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, (1 - 2 * d i) ^ (-(1 : ℝ) / 2) := by
  classical
  have hc := fun i => gaussian_sq_mgf (d i) (hd i)
  refine ⟨?_, ?_⟩
  · simp_rw [exp_sum]
    exact Integrable.fintype_prod_dep (fun i => (hc i).1)
  · simp_rw [exp_sum]
    rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => exp (d i * x ^ 2))]
    simp_rw [fun i => (hc i).2]

end TraceGaussianProof


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Hutchinson

namespace HutchinsonProof

lemma projection_square_mgf {n : ℕ} (α : Fin n → ℝ) (hα : α ⬝ᵥ α = 1)
    (t : ℝ) (ht : 0 ≤ t) (ht' : 2 * t < 1) :
    (∫ z, exp (t * (α ⬝ᵥ z) ^ 2) ∂rademacherVectorMeasure n) ≤
      (1 - 2 * t) ^ (-(1 : ℝ) / 2) := by
  classical
  let b := sqrt (2 * t)
  have hb : b ^ 2 = 2 * t := sq_sqrt (by positivity)
  have hsum : ∑ i, α i ^ 2 = 1 := by simpa [dotProduct, pow_two] using hα
  let R := rademacherVectorMeasure n
  let G := gaussianReal 0 1
  haveI : IsProbabilityMeasure R := by dsimp [R, rademacherVectorMeasure]; infer_instance
  let F := fun p : ℝ × (Fin n → ℝ) => exp (b * p.1 * (α ⬝ᵥ p.2))
  have hG := TraceGaussianProof.gaussian_sq_mgf t ht'
  have hmeas : Measurable F := by
    dsimp [F, dotProduct]
    fun_prop
  have hsection : ∀ g : ℝ, Integrable (fun z => F (g, z)) R ∧
      (∫ z, F (g, z) ∂ R) ≤ exp (t * g ^ 2) := by
    intro g
    refine ⟨integrable_pi_continuous _ (by dsimp [F, dotProduct]; fun_prop), ?_⟩
    have hh := rademacher_linear_mgf α (b * g)
    rw [hsum, mul_one] at hh
    have he : (b * g) ^ 2 / 2 = t * g ^ 2 := by rw [mul_pow, hb]; ring
    simpa only [R, rademacherVectorMeasure, F, dotProduct, he] using hh
  have hinner : Integrable (fun g => ∫ z, F (g, z) ∂ R) G := by
    refine hG.1.mono' hmeas.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_
    apply ae_of_all
    intro g
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => (exp_pos _).le))]
    exact (hsection g).2
  have hfull : Integrable F (G.prod R) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun g => (hsection g).1), ?_⟩
    simpa only [F, Real.norm_eq_abs, abs_of_pos (exp_pos _)] using hinner
  have he : ∀ z : Fin n → ℝ, (∫ g, F (g, z) ∂ G) = exp (t * (α ⬝ᵥ z) ^ 2) := by
    intro z
    have hr : (fun g => F (g, z)) = fun g => exp ((b * (α ⬝ᵥ z)) * g) := by
      funext g
      dsimp [F]
      congr 1
      ring
    rw [hr]
    have hh := congr_fun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (b * (α ⬝ᵥ z))
    simp only [mgf, NNReal.coe_one, zero_mul, zero_add, one_mul] at hh
    have hp : (b * (α ⬝ᵥ z)) ^ 2 / 2 = t * (α ⬝ᵥ z) ^ 2 := by
      rw [mul_pow, hb]
      ring
    simpa only [G, hp] using hh
  calc
    (∫ z, exp (t * (α ⬝ᵥ z) ^ 2) ∂ R) = ∫ g, ∫ z, F (g, z) ∂ R ∂ G := by
      simp_rw [← he]
      exact (integral_integral_swap hfull).symm
    _ ≤ ∫ g, exp (t * g ^ 2) ∂ G := integral_mono hinner hG.1 (fun g => (hsection g).2)
    _ = (1 - 2 * t) ^ (-(1 : ℝ) / 2) := hG.2

end HutchinsonProof


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Hutchinson

namespace HutchinsonProof

lemma projection_square_lower_mgf {n : ℕ} (α : Fin n → ℝ) (hα : α ⬝ᵥ α = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ z, exp (-t * (α ⬝ᵥ z) ^ 2) ∂rademacherVectorMeasure n) ≤ 1 - t + 3 / 2 * t ^ 2 := by
  have hm := projection_moments α hα
  have hi (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) : Integrable f (rademacherVectorMeasure n) :=
    integrable_pi_continuous f hf
  have hq2 : Integrable (fun z : Fin n → ℝ => (α ⬝ᵥ z) ^ 2) (rademacherVectorMeasure n) :=
    hi _ (by dsimp [dotProduct]; fun_prop)
  have hq4 : Integrable (fun z : Fin n → ℝ => (α ⬝ᵥ z) ^ 4) (rademacherVectorMeasure n) :=
    hi _ (by dsimp [dotProduct]; fun_prop)
  calc
    (∫ z, exp (-t * (α ⬝ᵥ z) ^ 2) ∂rademacherVectorMeasure n) ≤
        ∫ z, (1 - t * (α ⬝ᵥ z) ^ 2 + t ^ 2 / 2 * (α ⬝ᵥ z) ^ 4) ∂rademacherVectorMeasure n := by
      apply integral_mono (hi _ (by dsimp [dotProduct]; fun_prop))
        (hi _ (by dsimp [dotProduct]; fun_prop))
      intro z
      convert exp_neg_le_quadratic (t * (α ⬝ᵥ z) ^ 2) (mul_nonneg ht (sq_nonneg _)) using 1 <;>
        first | rfl | ring
    _ = 1 - t + t ^ 2 / 2 * (∫ z, (α ⬝ᵥ z) ^ 4 ∂rademacherVectorMeasure n) := by
      have hp : Integrable (fun z : Fin n → ℝ => 1 - t * (α ⬝ᵥ z) ^ 2) (rademacherVectorMeasure n) :=
        hi _ (by dsimp [dotProduct]; fun_prop)
      rw [integral_add hp (hq4.const_mul (t ^ 2 / 2)),
        integral_sub (integrable_const 1) (hq2.const_mul t), integral_const,
        integral_const_mul, integral_const_mul, hm.1]
      simp
    _ ≤ 1 - t + 3 / 2 * t ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hm.2 (sq_nonneg t)]

end HutchinsonProof


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Hutchinson

namespace HutchinsonProof

lemma product_projection_mgf {n : ℕ} (α : Fin n → ℝ) (M : ℕ) (t b : ℝ)
    (hb : (∫ z, exp (t * (α ⬝ᵥ z) ^ 2) ∂rademacherVectorMeasure n) ≤ exp b) :
    Integrable (fun ω => exp (t * ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2)) (hutchinsonSampleMeasure n M) ∧
    mgf (fun ω => ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2) (hutchinsonSampleMeasure n M) t ≤ exp ((M : ℝ) * b) := by
  classical
  have hi : Integrable (fun z : Fin n → ℝ => exp (t * (α ⬝ᵥ z) ^ 2)) (rademacherVectorMeasure n) :=
    integrable_pi_continuous _ (by dsimp [dotProduct]; fun_prop)
  have he : ∀ ω : Fin M → Fin n → ℝ,
      t * ∑ i, (α ⬝ᵥ ω i) ^ 2 = ∑ i, t * (α ⬝ᵥ ω i) ^ 2 := by
    intro ω
    rw [Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · unfold hutchinsonSampleMeasure
    simp_rw [he, exp_sum]
    exact Integrable.fintype_prod_dep (fun _ : Fin M => hi)
  · unfold mgf hutchinsonSampleMeasure
    simp_rw [he, exp_sum]
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin M) (z : Fin n → ℝ) => exp (t * (α ⬝ᵥ z) ^ 2))]
    calc
      (∏ _ : Fin M, ∫ z, exp (t * (α ⬝ᵥ z) ^ 2) ∂rademacherVectorMeasure n) ≤ ∏ _ : Fin M, exp b :=
        Finset.prod_le_prod (fun _ _ => integral_nonneg (fun _ => (exp_pos _).le)) (fun _ _ => hb)
      _ = exp ((M : ℝ) * b) := by
        rw [← exp_sum]
        simp [Finset.card_univ, Fintype.card_fin]

lemma chernoff_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → ℝ) (s u b : ℝ) (hs : 0 ≤ s)
    (hi : Integrable (fun ω => exp (s * Z ω)) P) (hb : mgf Z P s ≤ exp b) :
    P.real {ω | u ≤ Z ω} ≤ exp (-s * u + b) := by
  calc
    P.real {ω | u ≤ Z ω} ≤ exp (-s * u) * mgf Z P s := measure_ge_le_exp_mul_mgf u hs hi
    _ ≤ exp (-s * u) * exp b := mul_le_mul_of_nonneg_left hb (exp_pos _).le
    _ = exp (-s * u + b) := (exp_add _ _).symm

end HutchinsonProof


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Hutchinson

namespace HutchinsonProof

lemma achlioptas_bound {n : ℕ} (α : Fin n → ℝ) (hα : α ⬝ᵥ α = 1) (M : ℕ) (hM : 0 < M)
    (ε : ℝ) (hε : 0 < ε) :
    (hutchinsonSampleMeasure n M).real
      {ω | ε ≤ |(M : ℝ)⁻¹ * ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2 - 1|} ≤
        2 * exp (-((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
  classical
  let P := hutchinsonSampleMeasure n M
  haveI : IsProbabilityMeasure P := by dsimp [P, hutchinsonSampleMeasure]; infer_instance
  let X := fun ω : Fin M → Fin n → ℝ => ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2
  let t := ε / (2 * (1 + ε))
  have ht : 0 < t := by dsimp [t]; positivity
  have he0 : 0 < 1 + ε := by linarith
  have htE : t * (2 * (1 + ε)) = ε := by dsimp [t]; field_simp
  have ht' : 2 * t < 1 := by nlinarith [htE]
  have hd : 0 < 1 - 2 * t := by linarith
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hub : (∫ z, exp (t * (α ⬝ᵥ z) ^ 2) ∂rademacherVectorMeasure n) ≤
      exp (-log (1 - 2 * t) / 2) := by
    have hh := projection_square_mgf α hα t ht.le ht'
    convert hh using 1
    rw [rpow_def_of_pos hd]
    congr 1
    ring
  have hupMGF := product_projection_mgf α M t (-log (1 - 2 * t) / 2) hub
  have hupCost : -t * ((M : ℝ) * (1 + ε)) + (M : ℝ) * (-log (1 - 2 * t) / 2) ≤
      -((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3) := by
    have he : 1 - 2 * t = (1 + ε)⁻¹ := by dsimp [t]; field_simp; ring
    rw [he, log_inv]
    have hc := mul_le_mul_of_nonneg_left (log_one_add_cubic ε hε.le) hMpos.le
    nlinarith [htE]
  have hup : P.real {ω | (M : ℝ) * (1 + ε) ≤ X ω} ≤
      exp (-((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) :=
    (chernoff_bound P X t ((M : ℝ) * (1 + ε)) _ ht.le hupMGF.1 hupMGF.2).trans
      (exp_le_exp.mpr hupCost)
  let p := 1 - t + 3 / 2 * t ^ 2
  have hp : 0 < p := lower_poly_pos t
  have hlb : (∫ z, exp (-t * (α ⬝ᵥ z) ^ 2) ∂rademacherVectorMeasure n) ≤ exp (log p) := by
    rw [exp_log hp]
    exact projection_square_lower_mgf α hα t ht.le
  have hloMGF := product_projection_mgf α M (-t) (log p) hlb
  have hloCost : -t * ((M : ℝ) * (ε - 1)) + (M : ℝ) * log p ≤
      -((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3) := by
    have hlog := log_lower_poly t ht.le (by linarith)
    have hc := lower_parameter_cost ε hε.le
    change -ε * t + t ^ 2 + 4 / 3 * t ^ 3 ≤ -(ε ^ 2 / 4 - ε ^ 3 / 6) at hc
    have hlogM := mul_le_mul_of_nonneg_left hlog hMpos.le
    have hcM := mul_le_mul_of_nonneg_left hc hMpos.le
    dsimp [p]
    nlinarith
  have hli : Integrable (fun ω => exp (t * (-X ω))) P := by
    simpa only [X, mul_neg, neg_mul] using hloMGF.1
  have hlm : mgf (fun ω => -X ω) P t ≤ exp ((M : ℝ) * log p) := by
    simpa only [mgf, X, mul_neg, neg_mul] using hloMGF.2
  have hlo : P.real {ω | (M : ℝ) * (ε - 1) ≤ -X ω} ≤
      exp (-((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) :=
    (chernoff_bound P (fun ω => -X ω) t ((M : ℝ) * (ε - 1)) _ ht.le hli hlm).trans
      (exp_le_exp.mpr hloCost)
  have hsub : {ω | ε ≤ |(M : ℝ)⁻¹ * X ω - 1|} ⊆
      {ω | (M : ℝ) * (1 + ε) ≤ X ω} ∪ {ω | (M : ℝ) * (ε - 1) ≤ -X ω} := by
    intro ω hω
    change ε ≤ |(M : ℝ)⁻¹ * X ω - 1| at hω
    rcases le_abs.mp hω with h | h
    · left
      have hh := mul_le_mul_of_nonneg_left h hMpos.le
      have he : (M : ℝ) * ((M : ℝ)⁻¹ * X ω - 1) = X ω - M := by field_simp
      rw [he] at hh
      change (M : ℝ) * (1 + ε) ≤ X ω
      nlinarith
    · right
      have hh := mul_le_mul_of_nonneg_left h hMpos.le
      have he : (M : ℝ) * (-((M : ℝ)⁻¹ * X ω - 1)) = -X ω + M := by field_simp; ring
      rw [he] at hh
      change (M : ℝ) * (ε - 1) ≤ -X ω
      nlinarith
  calc
    P.real {ω | ε ≤ |(M : ℝ)⁻¹ * X ω - 1|} ≤
        P.real ({ω | (M : ℝ) * (1 + ε) ≤ X ω} ∪ {ω | (M : ℝ) * (ε - 1) ≤ -X ω}) :=
      measureReal_mono hsub
    _ ≤ P.real {ω | (M : ℝ) * (1 + ε) ≤ X ω} + P.real {ω | (M : ℝ) * (ε - 1) ≤ -X ω} :=
      measureReal_union_le _ _
    _ ≤ 2 * exp (-((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by linarith

end HutchinsonProof


open MeasureTheory ProbabilityTheory Real Matrix
open TraceEstimation.Hutchinson

namespace HutchinsonProof

lemma coordinate_bound {n : ℕ} (α : Fin n → ℝ) (hα : α ⬝ᵥ α = 1) (r : ℕ) (hr : 1 ≤ r)
    (ε δ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 < δ) (hδ' : δ < 1) (M : ℕ)
    (hMbound : 6 * ε⁻¹ ^ 2 * log (2 * (r : ℝ) / δ) ≤ (M : ℝ)) :
    (hutchinsonSampleMeasure n M).real
        {ω | ε ≤ |(M : ℝ)⁻¹ * ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2 - 1|} ≤ δ / r := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hl : 0 < log (2 * (r : ℝ) / δ) := by
    apply log_pos
    apply (lt_div_iff₀ hδ).mpr
    nlinarith
  have hMb : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hMbound
  have hM : 0 < M := by exact_mod_cast hMb
  have hc : -((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3) ≤ -(M : ℝ) * ε ^ 2 / 6 := by
    have hh : 0 ≤ (M : ℝ) * (ε ^ 2 * (1 / 2 - ε)) :=
      mul_nonneg hMb.le (mul_nonneg (sq_nonneg ε) (by linarith))
    nlinarith
  have hb := mul_le_mul_of_nonneg_right hMbound (sq_nonneg ε)
  have he : (6 * ε⁻¹ ^ 2 * log (2 * (r : ℝ) / δ)) * ε ^ 2 =
      6 * log (2 * (r : ℝ) / δ) := by field_simp [hε.ne']
  rw [he] at hb
  have hlog : log (2 * (r : ℝ) / δ) = -log (δ / (2 * (r : ℝ))) := by
    rw [log_div (by positivity) hδ.ne', log_div hδ.ne' (by positivity)]
    ring
  rw [hlog] at hb
  have hcost : -(M : ℝ) * ε ^ 2 / 6 ≤ log (δ / (2 * (r : ℝ))) := by linarith
  calc
    (hutchinsonSampleMeasure n M).real
        {ω | ε ≤ |(M : ℝ)⁻¹ * ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2 - 1|} ≤
      2 * exp (-((M : ℝ) / 2) * (ε ^ 2 / 2 - ε ^ 3 / 3)) := achlioptas_bound α hα M hM ε hε
    _ ≤ 2 * exp (-(M : ℝ) * ε ^ 2 / 6) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hc) (by norm_num)
    _ ≤ 2 * exp (log (δ / (2 * (r : ℝ)))) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hcost) (by norm_num)
    _ = δ / r := by rw [exp_log (by positivity)]; field_simp

end HutchinsonProof

open TraceEstimation TraceEstimation.Hutchinson
open MeasureTheory ProbabilityTheory Real Matrix

theorem solution {n : ℕ} (α : Fin n → ℝ) (hα : α ⬝ᵥ α = 1) (r : ℕ) (hr : 1 ≤ r)
    (ε δ : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 < δ) (hδ' : δ < 1) (M : ℕ)
    (hMbound : 6 * ε⁻¹ ^ 2 * Real.log (2 * (r : ℝ) / δ) ≤ (M : ℝ)) :
    (hutchinsonSampleMeasure n M).real
        {ω | ε ≤ |(M : ℝ)⁻¹ * ∑ i : Fin M, (α ⬝ᵥ ω i) ^ 2 - 1|} ≤ δ / r := by
  exact HutchinsonProof.coordinate_bound α hα r hr ε δ hε hε' hδ hδ' M hMbound
