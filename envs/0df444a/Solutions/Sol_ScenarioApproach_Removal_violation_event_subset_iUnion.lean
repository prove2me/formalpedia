-- Prove2me | solution 1 for ScenarioApproach.Removal.violation_event_subset_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:42:08.468993+00:00
-- url     : https://prove2.me/submissions/b320c5f0-7bfd-4d2d-9e25-f70739f05f18

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Removal_scenarioProgram

open MeasureTheory


namespace ScenarioApproach.Removal

lemma sw_feasible_eq {d N : ℕ} {Δ : Type*}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (ω : Fin N → Δ) (J : Finset (Fin N)) :
    feasibleSetWithout Θ Θδ ω J = feasibleSet Θ Θδ (fun j : Fin (Jᶜ).card => ω ((Jᶜ).equivFin.symm j).1) := by
  ext θ
  simp only [feasibleSetWithout, feasibleSet, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun j => h _ ?_⟩
    exact Finset.mem_compl.1 ((Jᶜ).equivFin.symm j).2
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun i hi => ?_⟩
    have hi' : i ∈ Jᶜ := by simpa using hi
    have := h ((Jᶜ).equivFin ⟨i, hi'⟩)
    simpa using this

lemma sw_unique {d N : ℕ} {Δ : Type*}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (hexu : ExistsUniqueSolution Θ Θδ c)
    (ω : Fin N → Δ) (J : Finset (Fin N)) (θ1 θ2 : EuclideanSpace ℝ (Fin d))
    (h1 : IsSolutionWithout Θ Θδ c ω J θ1) (h2 : IsSolutionWithout Θ Θδ c ω J θ2) : θ1 = θ2 := by
  have hf := sw_feasible_eq Θ Θδ ω J
  unfold IsSolutionWithout at h1 h2
  rw [hf] at h1 h2
  exact (hexu _ _).unique h1 h2

theorem violation_event_subset_iUnion_core {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (I : (Fin N → Δ) → Finset (Fin N)) (hIcard : ∀ ω, (I ω).card = k)
    (θk : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθk : ∀ ω, IsSolutionWithout Θ Θδ c ω (I ω) (θk ω))
    (hviol : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)), ∀ i ∈ I ω, θk ω ∉ Θδ (ω i))
    (θI : Finset (Fin N) → (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθI : ∀ J ω, IsSolutionWithout Θ Θδ c ω J (θI J ω))
    (ε : ℝ) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)),
      ω ∈ {ω : Fin N → Δ | ε < ScenarioApproach.Generalization.violation P Θδ (θk ω)} →
        ω ∈ ⋃ J ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
          {ω : Fin N → Δ | (∀ i ∈ J, θI J ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θI J ω)} := by
  filter_upwards [hviol] with ω hω hε
  have heq : θI (I ω) ω = θk ω := sw_unique Θ Θδ c hexu ω (I ω) _ _ (hθI _ _) (hθk ω)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨I ω, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hIcard ω⟩, ?_, ?_⟩
  · rw [heq]; exact hω
  · rw [heq]; exact hε

end ScenarioApproach.Removal

open ScenarioApproach.Removal


theorem solution {d N k : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d))
    (hexu : ExistsUniqueSolution Θ Θδ c)
    (I : (Fin N → Δ) → Finset (Fin N)) (hIcard : ∀ ω, (I ω).card = k)
    (θk : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθk : ∀ ω, IsSolutionWithout Θ Θδ c ω (I ω) (θk ω))
    (hviol : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)), ∀ i ∈ I ω, θk ω ∉ Θδ (ω i))
    (θI : Finset (Fin N) → (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθI : ∀ J ω, IsSolutionWithout Θ Θδ c ω J (θI J ω))
    (ε : ℝ) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => P)),
      ω ∈ {ω : Fin N → Δ | ε < ScenarioApproach.Generalization.violation P Θδ (θk ω)} →
        ω ∈ ⋃ J ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
          {ω : Fin N → Δ | (∀ i ∈ J, θI J ω ∉ Θδ (ω i)) ∧ ε < ScenarioApproach.Generalization.violation P Θδ (θI J ω)} := by
  exact violation_event_subset_iUnion_core P Θ Θδ c hexu I hIcard θk hθk hviol θI hθI ε
