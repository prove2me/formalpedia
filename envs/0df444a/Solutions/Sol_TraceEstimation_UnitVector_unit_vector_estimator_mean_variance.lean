-- Prove2me | solution 1 for TraceEstimation.UnitVector.unit_vector_estimator_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:35:39.152931+00:00
-- url     : https://prove2.me/submissions/925255e3-7195-4be3-a2dd-d6095899c656

import Definitions.Def_TraceEstimation_UnitVector_unitVectorEstimator
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Moments.SubGaussian

section

open MeasureTheory ProbabilityTheory Matrix Finset
namespace CTrace
open TraceEstimation.UnitVector

instance uniform_prob {n : ℕ} [NeZero n] : IsProbabilityMeasure (uniformIndex n) := by
  unfold uniformIndex
  infer_instance

instance sample_prob {n M : ℕ} [NeZero n] : IsProbabilityMeasure (indexSampleMeasure n M) := by
  unfold indexSampleMeasure
  infer_instance

theorem integral_uniform {n : ℕ} [NeZero n] (f : Fin n → ℝ) :
    (∫ i,f i ∂uniformIndex n)=(n : ℝ)⁻¹ * ∑ i,f i := by
  rw [integral_fintype ((MemLp.of_discrete (p:=1)).integrable le_rfl)]
  simp only [Measure.real,uniformIndex,uniformOn_univ,Measure.count_singleton,Fintype.card_fin,
    ENNReal.toReal_inv,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_natCast,one_div,smul_eq_mul,←Finset.mul_sum]

theorem integral_eval {n M : ℕ} [NeZero n] (f : Fin n → ℝ) (i : Fin M) :
    (∫ k,f (k i) ∂indexSampleMeasure n M)=(n : ℝ)⁻¹ * ∑ j,f j := by
  rw [←integral_uniform f]
  have hp:=measurePreserving_eval (fun _ : Fin M=>uniformIndex n) i
  rw [←hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable (by fun_prop)).symm

theorem estimator_diag {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin M → Fin n) :
    unitVectorEstimator A M k=(n : ℝ)/(M : ℝ)*∑ i,A (k i) (k i) := by
  simp [unitVectorEstimator,Matrix.mulVec_single,single_dotProduct]

theorem unit_mean {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    (∫ k,unitVectorEstimator A 1 k ∂indexSampleMeasure n 1)=A.trace := by
  simp only [estimator_diag,Nat.cast_one,div_one,Fin.sum_univ_one]
  rw [integral_const_mul]
  rw [integral_eval (fun i=>A i i) (0 : Fin 1)]
  have hn : (n : ℝ)≠0:=by exact_mod_cast NeZero.ne n
  rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
  rfl

theorem unit_variance {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    variance (unitVectorEstimator A 1) (indexSampleMeasure n 1)=
      (n : ℝ)*∑ i,A i i^2-A.trace^2 := by
  rw [variance_eq_sub (MemLp.of_discrete),unit_mean]
  congr 1
  change (∫ k,(unitVectorEstimator A 1 k)^2 ∂indexSampleMeasure n 1) = _
  simp only [estimator_diag,Nat.cast_one,div_one,Fin.sum_univ_one,mul_pow]
  rw [integral_const_mul]
  rw [integral_eval (fun i=>A i i^2) (0 : Fin 1)]
  have hn : (n : ℝ)≠0:=by exact_mod_cast NeZero.ne n
  field_simp

end CTrace
end

section

open MeasureTheory ProbabilityTheory Matrix TraceEstimation.UnitVector

theorem solution {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.IsSymm) :
    (∫ k,unitVectorEstimator A 1 k ∂indexSampleMeasure n 1)=A.trace ∧
      variance (unitVectorEstimator A 1) (indexSampleMeasure n 1)=
        (n : ℝ)*∑ i : Fin n,A i i^2-A.trace^2 := by
  haveI : NeZero n:=⟨hn.ne'⟩
  exact ⟨CTrace.unit_mean A,CTrace.unit_variance A⟩
end
