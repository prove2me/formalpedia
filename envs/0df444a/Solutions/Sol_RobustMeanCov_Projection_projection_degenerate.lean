-- Prove2me | solution 1 for RobustMeanCov.Projection.projection_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:41:55.1311+00:00
-- url     : https://prove2.me/submissions/b2ddbdf4-7b06-430d-8700-dc585232d245

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

theorem aux_pdeg_inner {n : ℕ} (x R : EuclideanSpace ℝ (Fin n)) :
    ⟪x, R⟫ = ∑ i, x i * R i := by
  simp [PiLp.inner_apply, mul_comm]

end RobustMeanCov.Projection

open RobustMeanCov.Projection
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

theorem solution {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hq : x.ofLp ⬝ᵥ S *ᵥ x.ofLp = 0)
    (P : Measure (EuclideanSpace ℝ (Fin n))) (hP : P ∈ MeanCovClass μ S) :
    ∀ᵐ R ∂P, ⟪x, R⟫ = ⟪x, μ⟫ := by
  obtain ⟨hprob, hL2, _hmean, hcov⟩ := hP
  set g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i R => R i - μ i with hg
  have hgL2 : ∀ i, MemLp (g i) 2 P := fun i => (hL2 i).sub (memLp_const _)
  have hgg : ∀ i j, Integrable (fun R => g i R * g j R) P := fun i j =>
    (hgL2 i).integrable_mul (hgL2 j)
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun R => ∑ i, x i * g i R with hf
  have hfR : ∀ R, ⟪x, R⟫ - ⟪x, μ⟫ = f R := by
    intro R
    simp only [aux_pdeg_inner, hf, hg, ← Finset.sum_sub_distrib, mul_sub]
  have hff : ∀ R, f R * f R = ∑ i, ∑ j, (x i * x j) * (g i R * g j R) := by
    intro R
    simp only [hf, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : Integrable (fun R => f R * f R) P := by
    simp_rw [hff]
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact (hgg i j).const_mul _
  have hval : ∫ R, f R * f R ∂P = 0 := by
    simp_rw [hff]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hgg i j).const_mul _]
    simp_rw [integral_finsetSum _ fun j _ => (hgg _ j).const_mul _]
    simp_rw [integral_const_mul]
    have : ∀ i j, ∫ R, g i R * g j R ∂P = S i j := fun i j => hcov i j
    simp_rw [this]
    rw [← hq]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hae : (fun R => f R * f R) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun R => mul_self_nonneg (f R)) hint).1 hval
  filter_upwards [hae] with R hR
  have h0 : f R = 0 := mul_self_eq_zero.1 hR
  have := hfR R
  linarith
