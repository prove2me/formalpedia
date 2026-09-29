-- Prove2me | solution 1 for RobustMeanCov.Projection.affine_image_mem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:13:00.296632+00:00
-- url     : https://prove2.me/submissions/fb3acefb-e1b3-457c-8f9e-da7176c037a8

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace RobustMeanCov.Projection

theorem aux_affm_coord {n : ℕ} (μ : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ)
    (Z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (μ + toEuclideanCLM (𝕜 := ℝ) A Z) i = μ i + ∑ k, A i k * Z k := by
  simp [ofLp_toEuclideanCLM, mulVec, dotProduct]

theorem aux_affm_sq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (i j : Fin n) :
    ∑ k, CFC.sqrt S i k * CFC.sqrt S j k = S i j := by
  have h1 : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self _ hS.nonneg
  have h2 : IsSelfAdjoint (CFC.sqrt S) := (CFC.sqrt_nonneg S).isSelfAdjoint
  have h3 : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    have := h2.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  conv_rhs => rw [← h1]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  conv_rhs => rw [← h3]
  rfl

end RobustMeanCov.Projection

open RobustMeanCov.Projection

theorem solution {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (Q : Measure (EuclideanSpace ℝ (Fin n)))
    (hQ : Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ)) :
    Q.map (fun Z => μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z) ∈ MeanCovClass μ S := by
  obtain ⟨hprob, hL2, hmean, hcov⟩ := hQ
  set A := CFC.sqrt S with hA
  have hmeas : Measurable (fun Z : EuclideanSpace ℝ (Fin n) => μ + toEuclideanCLM (𝕜 := ℝ) A Z) := by
    fun_prop
  have hcoordm : ∀ i : Fin n, Measurable (fun R : EuclideanSpace ℝ (Fin n) => R i) := by
    intro i; fun_prop
  have hint : ∀ k, Integrable (fun Z : EuclideanSpace ℝ (Fin n) => Z k) Q :=
    fun k => (hL2 k).integrable one_le_two
  have hint2 : ∀ k l, Integrable (fun Z : EuclideanSpace ℝ (Fin n) => Z k * Z l) Q :=
    fun k l => (hL2 k).integrable_mul (hL2 l)
  refine ⟨Measure.isProbabilityMeasure_map hmeas.aemeasurable, ?_, ?_, ?_⟩
  · intro i
    rw [memLp_map_measure_iff (hcoordm i).aestronglyMeasurable hmeas.aemeasurable]
    have : (fun R : EuclideanSpace ℝ (Fin n) => R i) ∘
        (fun Z : EuclideanSpace ℝ (Fin n) => μ + toEuclideanCLM (𝕜 := ℝ) A Z) =
        fun Z => μ i + ∑ k, A i k * Z k := funext fun Z => aux_affm_coord μ A Z i
    rw [this]
    have hs : MemLp (fun Z : EuclideanSpace ℝ (Fin n) => ∑ k, A i k * Z k) 2 Q := by
      have := memLp_finsetSum' (p := 2) (μ := Q) (Finset.univ : Finset (Fin n))
        (f := fun k (Z : EuclideanSpace ℝ (Fin n)) => A i k * Z k) (fun k _ => (hL2 k).const_mul (A i k))
      convert this using 1
      funext Z; simp [Finset.sum_apply]
    exact (memLp_const (μ i)).add hs
  · intro i
    rw [integral_map hmeas.aemeasurable (hcoordm i).aestronglyMeasurable]
    simp_rw [aux_affm_coord μ A _ i]
    rw [integral_add (integrable_const _)
      (integrable_finsetSum _ fun k _ => (hint k).const_mul _), integral_const,
      integral_finsetSum _ fun k _ => (hint k).const_mul _]
    simp_rw [integral_const_mul, hmean]
    simp
  · intro i j
    have hg : Measurable (fun R : EuclideanSpace ℝ (Fin n) => (R i - μ i) * (R j - μ j)) := by
      fun_prop
    rw [integral_map hmeas.aemeasurable hg.aestronglyMeasurable]
    simp_rw [aux_affm_coord μ A _ i, aux_affm_coord μ A _ j, add_sub_cancel_left,
      Finset.sum_mul_sum]
    have hterm : ∀ k l, ∫ Z : EuclideanSpace ℝ (Fin n), A i k * Z k * (A j l * Z l) ∂Q =
        A i k * A j l * (1 : Matrix (Fin n) (Fin n) ℝ) k l := by
      intro k l
      have h := hcov k l
      simp only [PiLp.zero_apply, sub_zero] at h
      rw [← h, ← integral_const_mul]
      congr 1; funext Z; ring
    have hI : ∀ k l, Integrable
        (fun Z : EuclideanSpace ℝ (Fin n) => A i k * Z k * (A j l * Z l)) Q := by
      intro k l
      have := (hint2 k l).const_mul (A i k * A j l)
      convert this using 1
      funext Z; ring
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => hI k l)]
    have hsum : ∀ k, ∫ Z : EuclideanSpace ℝ (Fin n), ∑ l, A i k * Z k * (A j l * Z l) ∂Q =
        ∑ l, A i k * A j l * (1 : Matrix (Fin n) (Fin n) ℝ) k l := by
      intro k
      rw [integral_finsetSum _ fun l _ => hI k l]
      exact Finset.sum_congr rfl fun l _ => hterm k l
    rw [Finset.sum_congr rfl fun k _ => hsum k]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [hA]
    exact aux_affm_sq S hS i j
