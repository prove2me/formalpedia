-- Prove2me | solution 1 for RobustMeanCov.Projection.projection_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:53:21.388878+00:00
-- url     : https://prove2.me/submissions/b7f440a6-6bbd-4e3e-a33c-138003589b1b

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

end RobustMeanCov.Projection

open RobustMeanCov.Projection

theorem solution {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) :
    Set.MapsTo (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
      (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) := by
  rintro P ⟨hP, hL, hmean, hcov⟩
  have hf : Continuous (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫) :=
    continuous_const.inner continuous_id
  have hfm : AEMeasurable (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫) P :=
    hf.measurable.aemeasurable
  have hfeq : (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫) = fun R => ∑ i, x i * R i := by
    ext R; simp [PiLp.inner_apply, mul_comm]
  have hint : ∀ i, Integrable (fun R : EuclideanSpace ℝ (Fin n) => R i) P :=
    fun i => (hL i).integrable one_le_two
  have hLc : ∀ i, MemLp (fun R : EuclideanSpace ℝ (Fin n) => R i - μ i) 2 P :=
    fun i => (hL i).sub (memLp_const _)
  have hij : ∀ i j, Integrable
      (fun R : EuclideanSpace ℝ (Fin n) => (R i - μ i) * (R j - μ j)) P :=
    fun i j => (hLc i).integrable_mul (hLc j)
  have hμ : ⟪x, μ⟫ = ∑ i, x i * μ i := by simp [PiLp.inner_apply, mul_comm]
  refine ⟨Measure.isProbabilityMeasure_map hfm, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [memLp_map_measure_iff (g := fun r : ℝ => r) aestronglyMeasurable_id hfm]
    have : (fun r : ℝ => r) ∘ (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫)
        = fun R => ∑ i, x i * R i := by rw [← hfeq]; rfl
    rw [this]
    exact memLp_finsetSum _ (fun i _ => (hL i).const_mul (x i))
  · rw [integral_map (f := fun r : ℝ => r) hfm aestronglyMeasurable_id, hfeq, integral_finsetSum _
      (fun i _ => (hint i).const_mul (x i)), hμ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, hmean]
  · rw [integral_map (f := fun r : ℝ => (r - ⟪x, μ⟫) ^ 2) hfm (by fun_prop)]
    have hsq : (fun R : EuclideanSpace ℝ (Fin n) => (⟪x, R⟫ - ⟪x, μ⟫) ^ 2)
        = fun R => ∑ i, ∑ j, (x i * x j) * ((R i - μ i) * (R j - μ j)) := by
      ext R
      rw [show ⟪x, R⟫ = ∑ i, x i * R i from congrFun hfeq R, hμ, ← Finset.sum_sub_distrib, sq,
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    rw [hsq, integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hij i j).const_mul _))]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => (hij i j).const_mul _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul, hcov]
    ring
