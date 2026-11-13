-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_edge_properties
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:50:43.325235+00:00
-- url     : https://prove2.me/submissions/2dd1dd9e-fb11-4600-a969-5ac45f930bc6

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_affine_factors
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical BigOperators
open MeasureTheory Set ZeroFreeRRG.Hardcore

private noncomputable def affine (q : ℕ) (c : ℝ) (μ : Fin q → ℝ) : Fin q → ℝ :=
  fun i => (1-c)*(q:ℝ)⁻¹+c*μ i

private theorem affine_cont (q : ℕ) (c : ℝ) : Continuous (affine q c) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul (continuous_apply i))

private theorem vertex_cont (q d : ℕ) (β : ℝ) :
    Continuous (fun μs : Fin d → Fin q → ℝ => vertexFactor (.potts q) β d μs) := by
  unfold vertexFactor Mmul
  fun_prop

private theorem edge_cont (q : ℕ) (β : ℝ) :
    Continuous (fun p : (Fin q → ℝ) × (Fin q → ℝ) => edgeFactor (.potts q) β p.1 p.2) := by
  unfold edgeFactor
  fun_prop

private theorem vertex_entropy_cont (q d : ℕ) (β : ℝ) :
    Continuous (fun μs : Fin d → Fin q → ℝ => xlogx (vertexFactor (.potts q) β d μs)) :=
  Real.continuous_mul_log.comp (vertex_cont q d β)

private theorem edge_entropy_cont (q : ℕ) (β : ℝ) :
    Continuous (fun p : (Fin q → ℝ) × (Fin q → ℝ) => xlogx (edgeFactor (.potts q) β p.1 p.2)) :=
  Real.continuous_mul_log.comp (edge_cont q β)

private theorem simplex_ae (q : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β) :
    ∀ᵐ μ ∂(ν : Measure (Fin q → ℝ)), μ ∈ stdSimplex ℝ (Fin q) := by
  exact ae_iff.mpr hν.1

private theorem simplex_pi_ae (q d : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β) :
    ∀ᵐ xs ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ))),
      ∀ i, xs i ∈ stdSimplex ℝ (Fin q) := by
  apply Measure.ae_pi_le_pi
  apply Filter.eventually_pi
  intro i
  exact simplex_ae q β ν hν

private theorem simplex_pair_ae (q : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β) :
    ∀ᵐ p ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))),
      p.1 ∈ stdSimplex ℝ (Fin q) ∧ p.2 ∈ stdSimplex ℝ (Fin q) := by
  have hs : MeasurableSet (stdSimplex ℝ (Fin q)) := (isClosed_stdSimplex ℝ (Fin q)).measurableSet
  apply (Measure.ae_prod_iff_ae_ae (hs.prod hs)).2
  filter_upwards [simplex_ae q β ν hν] with x hx
  filter_upwards [simplex_ae q β ν hν] with y hy
  exact ⟨hx,hy⟩


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

/-- The Potts edge factor has mean one under two independent cavity messages. -/
theorem potts_edge_mean_one (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hb : 0 ≤ β)
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β) :
    (∫ p, edgeFactor (.potts q) β p.1 p.2
      ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) = 1 := by
  classical
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have htpos : 0 < (q:ℝ)-1+β := by linarith
  have ht : (q:ℝ)-1+β ≠ 0 := by linarith
  have hint (i j : Fin q) : Integrable
      (fun p : (Fin q → ℝ) × (Fin q → ℝ) =>
        p.1 i * (Model.M (.potts q) β i j * p.2 j))
      ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) :=
    (coord_integrable q β ν hν i).mul_prod ((coord_integrable q β ν hν j).const_mul _)
  have hsum_int (i : Fin q) : Integrable
      (fun p : (Fin q → ℝ) × (Fin q → ℝ) =>
        ∑ j : Fin q, p.1 i * (Model.M (.potts q) β i j * p.2 j))
      ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) :=
    integrable_finset_sum _ (fun j _ => hint i j)
  have hterm (i j : Fin q) :
      (∫ p : (Fin q → ℝ) × (Fin q → ℝ),
        p.1 i * (Model.M (.potts q) β i j * p.2 j)
        ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) = Model.P (.potts q) β i j := by
    have hh := integral_prod_mul (μ := (ν : Measure (Fin q → ℝ)))
      (ν := (ν : Measure (Fin q → ℝ))) (fun x : Fin q → ℝ => x i)
      (fun y : Fin q → ℝ => Model.M (.potts q) β i j * y j)
    have hm1 : (∫ x : Fin q → ℝ, x i ∂(ν : Measure (Fin q → ℝ))) = Model.pi (.potts q) β i := hν.2 i
    have hm2 : (∫ x : Fin q → ℝ, x j ∂(ν : Measure (Fin q → ℝ))) = Model.pi (.potts q) β j := hν.2 j
    rw [hh, integral_const_mul, hm1, hm2]
    unfold Model.M
    rw [potts_pi_real q β i hqn ht, potts_pi_real q β j hqn ht]
    field_simp
  have heq : (∫ p, edgeFactor (.potts q) β p.1 p.2
      ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) =
      ∑ i : Fin q, ∑ j : Fin q, Model.P (.potts q) β i j := by
    change (∫ p : (Fin q → ℝ) × (Fin q → ℝ),
      ∑ i : Fin q, ∑ j : Fin q, p.1 i * Model.M (.potts q) β i j * p.2 j
      ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) = _
    simp_rw [mul_assoc]
    rw [integral_finset_sum _ (fun i _ => hsum_int i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finset_sum _ (fun j _ => hint i j)]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm i j
  rw [heq]
  change (∑ i : Fin q, Model.pi (.potts q) β i) = 1
  simp [potts_pi_real q β _ hqn ht, hqn]

/-- The Potts edge factor is nonnegative on probability messages for β ≥ 0. -/
theorem potts_edge_nonneg (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hb : 0 ≤ β)
    (μ ξ : Fin q → ℝ) (hμ : μ ∈ stdSimplex ℝ (Fin q))
    (hξ : ξ ∈ stdSimplex ℝ (Fin q)) : 0 ≤ edgeFactor (.potts q) β μ ξ := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  have htpos : 0 < (q:ℝ)-1+β := by linarith
  have ht : (q:ℝ)-1+β ≠ 0 := by linarith
  have hm (i j : Fin q) : 0 ≤ Model.M (.potts q) β i j := by
    unfold Model.M
    rw [potts_pi_real q β i hqn ht,potts_pi_real q β j hqn ht]
    apply div_nonneg
    · change 0 ≤ ((1:ℝ) + if i=j then β-1 else 0) / ((q:ℝ)*((q:ℝ)-1+β))
      apply div_nonneg _ (by positivity)
      by_cases h : i=j <;> simp [h] <;> linarith
    · positivity
  unfold edgeFactor
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (hμ.1 i) (hm i j)) (hξ.1 j)

/-- Continuous functions of a pair of cavity messages are integrable. -/
theorem potts_pair_integrable (q : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β)
    (F : (Fin q → ℝ) × (Fin q → ℝ) → ℝ) (hF : Continuous F) :
    Integrable F ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) := by
  have hK : IsCompact (stdSimplex ℝ (Fin q) ×ˢ stdSimplex ℝ (Fin q)) :=
    (isCompact_stdSimplex ℝ (Fin q)).prod (isCompact_stdSimplex ℝ (Fin q))
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  apply Integrable.of_bound hF.aestronglyMeasurable C
  filter_upwards [simplex_pair_ae q β ν hν] with p hp
  exact hC p hp

/-- Mean, positivity, and integrability needed for the Bethe entropy comparison. -/
theorem solution (q : ℕ) (hq : 2 ≤ q) (β c : ℝ) (hb : 0 ≤ β)
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β) :
    (∫ p, edgeFactor (.potts q) β p.1 p.2
      ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) = 1 ∧
    (∀ᵐ p ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))),
      0 ≤ edgeFactor (.potts q) β p.1 p.2) ∧
    Integrable (fun p => edgeFactor (.potts q) β p.1 p.2)
      ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) ∧
    Integrable (fun p => xlogx (edgeFactor (.potts q) β p.1 p.2))
      ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) ∧
    Integrable (fun p => xlogx (1-c+c*edgeFactor (.potts q) β p.1 p.2))
      ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) := by
  refine ⟨potts_edge_mean_one q hq β hb ν hν, ?_, ?_, ?_, ?_⟩
  · filter_upwards [simplex_pair_ae q β ν hν] with p hp
    exact potts_edge_nonneg q hq β hb p.1 p.2 hp.1 hp.2
  · exact potts_pair_integrable q β ν hν _ (edge_cont q β)
  · exact potts_pair_integrable q β ν hν _ (edge_entropy_cont q β)
  · exact potts_pair_integrable q β ν hν _
      (Real.continuous_mul_log.comp (continuous_const.add (continuous_const.mul (edge_cont q β))))
