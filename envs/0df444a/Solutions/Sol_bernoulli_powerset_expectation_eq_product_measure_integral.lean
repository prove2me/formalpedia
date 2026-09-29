-- Prove2me | solution 1 for bernoulli_powerset_expectation_eq_product_measure_integral
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T03:08:17.747933+00:00
-- url     : https://prove2.me/submissions/c2028219-2a5c-4b67-89b4-dba381481a4d

import Definitions.Def_matrix_completion_bernoulli_measure
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace KeystoneBridge

/-- Real-valued single-point mass of one Bernoulli factor. -/
private lemma bern_factor_real (p : NNReal) (hp : p ≤ 1) (b : Bool) :
    ((PMF.bernoulli p hp).toMeasure.real {b}) = (cond b p (1 - p) : NNReal) := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  rw [PMF.bernoulli_apply, ENNReal.coe_toReal]

/-- Single-point mass of the product measure factorizes over coordinates. -/
private lemma bernMeasure_real_singleton {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (ω : (Fin n1 × Fin n2) → Bool) :
    (bernMeasure p hp).real {ω} = ∏ w, ((cond (ω w) p (1 - p) : NNReal) : ℝ) := by
  rw [measureReal_def, bernMeasure, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro w _
  rw [← measureReal_def, bern_factor_real]

/-- The product weight at a Finset equals the Bernoulli observation weight. -/
private lemma prod_cond_toIndic_eq_weight {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (Ω : Finset (Fin n1 × Fin n2)) :
    ∏ w, ((cond (finsetToIndicator Ω w) p (1 - p) : NNReal) : ℝ)
      = bernoulliObservationWeight (p : ℝ) Ω := by
  have hcoe : (((1 - p : NNReal)) : ℝ) = 1 - (p : ℝ) := by
    rw [NNReal.coe_sub hp, NNReal.coe_one]
  have hsplit : ∏ w, ((cond (finsetToIndicator Ω w) p (1 - p) : NNReal) : ℝ)
      = (∏ _w ∈ Ω, ((p : NNReal) : ℝ)) * ∏ _w ∈ Ωᶜ, (((1 - p : NNReal)) : ℝ) := by
    rw [← Finset.prod_mul_prod_compl Ω]
    congr 1
    · apply Finset.prod_congr rfl; intro w hw
      have : finsetToIndicator Ω w = true := by simp [finsetToIndicator, hw]
      rw [this]; rfl
    · apply Finset.prod_congr rfl; intro w hw
      simp only [Finset.mem_compl] at hw
      have : finsetToIndicator Ω w = false := by simp [finsetToIndicator, hw]
      rw [this]; rfl
  rw [hsplit, Finset.prod_const, Finset.prod_const, hcoe, bernoulliObservationWeight,
      Finset.card_compl]

end KeystoneBridge

open KeystoneBridge in
theorem solution
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (F : Finset (Fin n1 × Fin n2) → ℝ) :
    bernoulliExpectation (p : ℝ) F
      = ∫ ω, F (indicatorToFinset ω) ∂(bernMeasure p hp) := by
  have hint : ∫ ω, F (indicatorToFinset ω) ∂(bernMeasure p hp)
      = ∑ ω, (bernMeasure p hp).real {ω} • F (indicatorToFinset ω) :=
    MeasureTheory.integral_fintype (μ := bernMeasure p hp)
      (f := fun ω => F (indicatorToFinset ω)) Integrable.of_finite
  rw [hint, bernoulliExpectation]
  rw [← Equiv.sum_comp indicatorFinsetEquiv
        (fun Ω => bernoulliObservationWeight (p : ℝ) Ω * F Ω)]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [indicatorFinsetEquiv, Equiv.coe_fn_mk, smul_eq_mul]
  rw [bernMeasure_real_singleton p hp ω]
  have key : (∏ w, ((cond (ω w) p (1 - p) : NNReal) : ℝ))
      = bernoulliObservationWeight (p : ℝ) (indicatorToFinset ω) := by
    have := prod_cond_toIndic_eq_weight p hp (indicatorToFinset ω)
    rwa [finsetToIndicator_indicatorToFinset ω] at this
  rw [key]
