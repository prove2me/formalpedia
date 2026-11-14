-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.coloring_vertex_factor_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:44:19.360587+00:00
-- url     : https://prove2.me/submissions/56bbf17d-2c4a-49a6-b469-cfc43aa35858

import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_observation_density
import Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_vertex_density_mixture
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical BigOperators
open MeasureTheory Set ZeroFreeRRG.Hardcore

theorem solution (q d : ℕ) (hq : 3 ≤ q) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) :
    (∫ xs, vertexFactor (.potts q) 0 d xs
      ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ)))) = 1 := by
  classical
  let μ := (ν : Measure (Fin q → ℝ))
  let w : Fin q → (Fin q → ℝ) → ℝ := fun i x => (q:ℝ)*(1-x i)/((q:ℝ)-1)
  have ho := coloring_observation_density q hq ν hν
  have hi (i : Fin q) : Integrable (w i) μ := (ho.1 i).2.1
  have hm (i : Fin q) : (∫ x, w i x ∂μ) = 1 := (ho.1 i).2.2
  have hs : ∀ᵐ x ∂μ, x ∈ stdSimplex ℝ (Fin q) := ae_iff.mpr hν.1
  have hpi : ∀ᵐ xs ∂(Measure.pi fun _ : Fin d => μ), ∀ j, xs j ∈ stdSimplex ℝ (Fin q) := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ => hs)
  have hprod (i : Fin q) : Integrable (fun xs : Fin d → Fin q → ℝ => ∏ j, w i (xs j))
      (Measure.pi fun _ : Fin d => μ) := by
    apply Integrable.fin_nat_prod
    intro j
    exact hi i
  have heq : (∫ xs, vertexFactor (.potts q) 0 d xs ∂(Measure.pi fun _ : Fin d => μ)) =
      ∫ xs, (q:ℝ)⁻¹ * ∑ i : Fin q, ∏ j : Fin d, w i (xs j)
        ∂(Measure.pi fun _ : Fin d => μ) := by
    apply integral_congr_ae
    filter_upwards [hpi] with xs hs'
    exact coloring_vertex_density_mixture q d hq xs (fun j => (hs' j).2)
  rw [heq, integral_const_mul, integral_finsetSum _ (fun i hi' => hprod i)]
  have hprodmean (i : Fin q) :
      (∫ xs : Fin d → Fin q → ℝ, ∏ j : Fin d, w i (xs j)
        ∂(Measure.pi fun _ : Fin d => μ)) = 1 := by
    rw [integral_fin_nat_prod_eq_prod]
    simp [hm]
  simp only [hprodmean, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hqn : (q:ℝ) ≠ 0 := by
    have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  field_simp
