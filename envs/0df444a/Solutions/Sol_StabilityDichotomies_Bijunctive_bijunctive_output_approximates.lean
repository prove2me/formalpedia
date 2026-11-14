-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_output_approximates
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:00:25.723208+00:00
-- url     : https://prove2.me/submissions/d47e22c9-3bdc-48e7-b717-3ad2f169c8a8

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_occurrence_violation_seed_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_is_probability
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_event_measurable
import Theorems.Thm_StabilityDichotomies_Solvability_approximation_of_constraint_bounds
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution (Γ : Language) (rep : TwoCNFRepresentation Γ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (A : Solver Γ)
    (hLaw : BijunctiveOutputLaw Γ rep ε A) : Approximates A ε := by
  classical
  apply approximation_of_constraint_bounds Γ A ε
  intro V _ I hI c hc
  obtain ⟨j,hj⟩ := List.get_of_mem (Multiset.mem_toList.mpr hc)
  let i : Fin I.constraints.card := ⟨j.val, by simpa using j.isLt⟩
  have hi : occurrenceAt I i = c := by simpa [occurrenceAt, i] using hj
  let μ := bijunctiveSeedMeasure rep I ε
  letI : IsProbabilityMeasure μ := bijunctive_seed_is_probability rep I ε hε
  let f := fun s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
    bijunctiveOutput rep I ε s.1 s.2.1 s.2.2
  let B : Finset (V → Bool) := Finset.univ.filter (fun x => ¬ c.Satisfied x)
  have hsum : (∑ x : V → Bool, (A V I x).toReal * (if ¬ c.Satisfied x then (1 : ℝ) else 0)) =
      ∑ x ∈ B, μ.real (f ⁻¹' {x}) := by
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    change (∑ x ∈ B, (A V I x).toReal) = _
    apply Finset.sum_congr rfl
    intro x hx
    have hlaw := hLaw V I hI x
    exact hlaw
  have hm (x : V → Bool) (hx : x ∈ B) : MeasurableSet (f ⁻¹' {x}) := by
    change MeasurableSet {s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 = x}
    exact bijunctive_output_event_measurable rep I ε x
  have heq := sum_measureReal_preimage_singleton (μ := μ) B hm
  have hevent : f ⁻¹' (B : Set (V → Bool)) =
      {seed | ¬ c.Satisfied (bijunctiveOutput rep I ε seed.1 seed.2.1 seed.2.2)} := by
    ext seed
    simp [B,f]
  rw [hsum,heq,hevent]
  have hb := bijunctive_occurrence_violation_seed_bound rep I hI ε hε hε1 i
  rw [hi] at hb
  exact hb
