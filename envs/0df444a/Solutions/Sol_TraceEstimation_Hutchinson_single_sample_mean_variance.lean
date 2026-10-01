-- Prove2me | solution 1 for TraceEstimation.Hutchinson.single_sample_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:18:54.351668+00:00
-- url     : https://prove2.me/submissions/41771bbf-f8de-4b35-87f2-577f493d4590

import Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

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
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (MemLp (fun z : Fin n → ℝ => z ⬝ᵥ (A *ᵥ z)) 2 (rademacherVectorMeasure n) ∧
      ∫ z, z ⬝ᵥ (A *ᵥ z) ∂(rademacherVectorMeasure n) = A.trace) ∧
    (A.IsSymm →
      variance (fun z : Fin n → ℝ => z ⬝ᵥ (A *ᵥ z)) (rademacherVectorMeasure n) =
        2 * (∑ i, ∑ j, A i j ^ 2 - ∑ i, A i i ^ 2)) := by
  exact ⟨⟨CTraceHutch.quadratic_memLp A,CTraceHutch.quadratic_mean A⟩,CTraceHutch.quadratic_variance A⟩
end
