-- Prove2me | solution 1 for WorstCaseVaR.Entropy.gaussian_tail_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:54:57.528115+00:00
-- url     : https://prove2.me/submissions/2e8a33d4-65b9-4c44-8b59-c0decea2b0e6

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy
open MeasureTheory ProbabilityTheory

theorem aux_gte_cov {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) : covarianceBilin (multivariateGaussian xhat Γ) w w = quadForm Γ w := by
  rw [covarianceBilin_multivariateGaussian hΓ.posSemidef]
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_gte_pos {n : ℕ} (w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) : 0 < quadForm Γ w := by
  have h := hΓ.dotProduct_mulVec_pos (x := w.ofLp) (by simpa using hw)
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, star_trivial] at h
  refine lt_of_lt_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_gte_quad_neg {n : ℕ} (w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ) :
    quadForm Γ (-w) = quadForm Γ w := by
  unfold quadForm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp

theorem aux_gte_map {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) :
    (multivariateGaussian xhat Γ).map (innerSL ℝ w) =
      gaussianReal (inner ℝ w xhat) (quadForm Γ w).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal]
  congr 1
  · rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id]
    simp
  · rw [← aux_gte_cov xhat w Γ hΓ, covarianceBilin_self IsGaussian.memLp_two_id]
    rfl

/-- standardization -/
theorem aux_gte_std (m : ℝ) (v : ℝ) (hv : 0 < v) (γ : ℝ) :
    (gaussianReal m v.toNNReal).real (Set.Ici γ) =
      1 - cdf (gaussianReal 0 1) ((γ - m) / Real.sqrt v) := by
  have hσ : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hrep : gaussianReal m v.toNNReal =
      (gaussianReal 0 1).map (fun x => Real.sqrt v * x + m) := by
    have : (fun x => Real.sqrt v * x + m) = (· + m) ∘ (Real.sqrt v * ·) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt hv.le, hv.le]
  rw [hrep, map_measureReal_apply (by fun_prop) measurableSet_Ici]
  have hpre : (fun x => Real.sqrt v * x + m) ⁻¹' Set.Ici γ = Set.Ici ((γ - m) / Real.sqrt v) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici]
    rw [div_le_iff₀ hσ]
    constructor <;> intro h <;> linarith
  rw [hpre, cdf_eq_real]
  have := nullSingletonClass_gaussianReal (μ := (0:ℝ)) (v := 1) one_ne_zero
  rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
    measureReal_congr Iio_ae_eq_Iic]

end WorstCaseVaR.Entropy

open WorstCaseVaR.Entropy
open MeasureTheory ProbabilityTheory

theorem solution {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (γ : ℝ) :
    (refGaussian xhat Γ).real (lossSet w γ) = gaussianTail xhat Γ w γ := by
  have hset : lossSet w γ = (innerSL ℝ (-w)) ⁻¹' Set.Ici γ := by
    ext x
    simp [lossSet, real_inner_comm]
  rw [refGaussian, hset, ← map_measureReal_apply (by fun_prop) measurableSet_Ici,
    aux_gte_map xhat (-w) Γ hΓ, aux_gte_quad_neg,
    aux_gte_std _ _ (aux_gte_pos w Γ hΓ hw), gaussianTail, stdNormalCDF]
  congr 2
  simp [inner_neg_left]
