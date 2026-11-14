-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.coloring_observation_density
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:33:50.303057+00:00
-- url     : https://prove2.me/submissions/9cca556c-79d7-4e0b-b066-7e84e1810cbc

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_affine_factors
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical BigOperators
open MeasureTheory Set ZeroFreeRRG.Hardcore

private theorem simplex_ae (q : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β) :
    ∀ᵐ μ ∂(ν : Measure (Fin q → ℝ)), μ ∈ stdSimplex ℝ (Fin q) := by
  exact ae_iff.mpr hν.1

private lemma potts_pi_real (q : ℕ) (β : ℝ) (i : Fin q)
    (hq : (q:ℝ) ≠ 0) (ht : (q:ℝ) - 1 + β ≠ 0) :
    Model.pi (.potts q) β i = (q:ℝ)⁻¹ := by
  unfold Model.pi Model.P
  change (∑ j : Fin q, ((1:ℝ) + if i = j then β - 1 else 0) /
      ((q:ℝ) * ((q:ℝ) - 1 + β))) = (q:ℝ)⁻¹
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hs : (∑ j : Fin q, if i = j then β - 1 else 0) = β - 1 := by simp
  rw [hs]
  field_simp
  ring


private theorem coord_integrable (q : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β) (i : Fin q) :
    Integrable (fun μ : Fin q → ℝ => μ i) (ν : Measure (Fin q → ℝ)) := by
  apply Integrable.of_bound (continuous_apply i).aestronglyMeasurable 1
  filter_upwards [simplex_ae q β ν hν] with μ hμ
  have hh := mem_Icc_of_mem_stdSimplex hμ i
  simpa [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2



theorem solution (q : ℕ) (hq : 3 ≤ q) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) :
    (∀ i : Fin q,
      (∀ᵐ x ∂(ν : Measure (Fin q → ℝ)), 0 ≤ (q:ℝ)*(1-x i)/((q:ℝ)-1)) ∧
      Integrable (fun x => (q:ℝ)*(1-x i)/((q:ℝ)-1)) (ν : Measure (Fin q → ℝ)) ∧
      (∫ x, (q:ℝ)*(1-x i)/((q:ℝ)-1) ∂(ν : Measure (Fin q → ℝ))) = 1) ∧
    (∀ x ∈ stdSimplex ℝ (Fin q),
      (∑ i : Fin q, (q:ℝ)*(1-x i)/((q:ℝ)-1)) = q) := by
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have hden : (q:ℝ)-1 ≠ 0 := by linarith
  constructor
  · intro i
    have hcoord := coord_integrable q 0 ν hν i
    have hp : Model.pi (.potts q) (0:ℝ) i = (q:ℝ)⁻¹ := by
      apply potts_pi_real q 0 i hqn
      linarith
    have hmean : (∫ x, x i ∂(ν : Measure (Fin q → ℝ))) = (q:ℝ)⁻¹ := (hν.2 i).trans hp
    constructor
    · filter_upwards [simplex_ae q 0 ν hν] with x hx
      have hb := mem_Icc_of_mem_stdSimplex hx i
      exact div_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hb.2)) (by linarith)
    · constructor
      · convert ((integrable_const 1).sub hcoord).const_mul ((q:ℝ)/((q:ℝ)-1)) using 1
        funext x
        dsimp
        ring
      · have heq : (fun x : Fin q → ℝ => (q:ℝ)*(1-x i)/((q:ℝ)-1)) =
            fun x => ((q:ℝ)/((q:ℝ)-1))*(1-x i) := by funext x; ring
        rw [heq, integral_const_mul, integral_sub (integrable_const 1) hcoord, hmean]
        simp only [integral_const, probReal_univ, one_smul]
        field_simp
  · intro x hx
    rw [← Finset.sum_div]
    simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hx.2]
    field_simp
