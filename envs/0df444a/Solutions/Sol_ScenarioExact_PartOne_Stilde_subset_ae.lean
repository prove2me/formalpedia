-- Prove2me | solution 1 for ScenarioExact.PartOne.Stilde_subset_ae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:31:42.684254+00:00
-- url     : https://prove2.me/submissions/781a2e8f-b46d-4fb8-a690-56676299a037

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

open MeasureTheory ScenarioApproach.Generalization ScenarioExact.PartOne in
theorem solution {d m : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hexu : ∀ (k : ℕ) (ω : Fin k → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    (θs : (k : ℕ) → (Fin k → Δ) → EuclideanSpace ℝ (Fin d))
    (hθs : ∀ (k : ℕ) (ω : Fin k → Δ), IsSolution c Θ Θδ ω (θs k ω))
    (hfs : FullySupported c Θ Θδ P)
    (hm : d ≤ m) :
    Measure.pi (fun _ : Fin m => P) (Stilde Θδ θs hm \ S c Θ Θδ θs (Ibar d m)) = 0 := by
  classical
  have hae := hfs m hm
  rw [ae_iff] at hae
  refine measure_mono_null ?_ hae
  rintro ω ⟨hSt, hnS⟩
  simp only [Set.mem_setOf_eq]
  intro hall
  apply hnS
  show supportIndexSet c Θ Θδ ω (θs m ω) = Ibar d m
  have hnum : (supportIndexSet c Θ Θδ ω (θs m ω)).card = d := hall _ (hθs m ω)
  obtain ⟨⟨hxΘ, hxI⟩, hxopt⟩ := hθs d (firstD hm ω)
  obtain ⟨_, hmopt⟩ := hθs m ω
  have hxfeas : θs d (firstD hm ω) ∈ feasibleSet Θ Θδ ω := by
    refine ⟨hxΘ, Set.mem_iInter.2 fun j => ?_⟩
    by_cases hj : d ≤ j.val
    · exact hSt j hj
    · have h := Set.mem_iInter.1 hxI ⟨j.val, by omega⟩
      have hj' : Fin.castLE hm ⟨j.val, by omega⟩ = j := Fin.ext rfl
      simpa only [firstD, hj'] using h
  have hle : inner ℝ c (θs m ω) ≤ inner ℝ c (θs d (firstD hm ω)) := hmopt _ hxfeas
  have hsub : supportIndexSet c Θ Θδ ω (θs m ω) ⊆ Ibar d m := by
    intro j hj
    unfold supportIndexSet at hj
    rw [Finset.mem_filter] at hj
    unfold Ibar
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hjd
    push_neg at hjd
    obtain ⟨θ, hθΘ, hθj, hlt⟩ := hj.2
    have hfeas : θ ∈ feasibleSet Θ Θδ (firstD hm ω) := by
      refine ⟨hθΘ, Set.mem_iInter.2 fun i => ?_⟩
      refine hθj _ ?_
      intro h
      have := congrArg Fin.val h
      simp only [Fin.coe_castLE] at this
      omega
    have := hxopt θ hfeas
    linarith
  have hcard : (Ibar d m).card ≤ (supportIndexSet c Θ Θδ ω (θs m ω)).card := by
    rw [hnum]
    calc (Ibar d m).card ≤ (Finset.range d).card :=
          Finset.card_le_card_of_injOn (fun i => i.val)
            (by
              intro i hi
              simp only [Ibar, Finset.coe_filter, Finset.mem_univ, true_and,
                Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio] at hi ⊢
              exact hi)
            (fun a _ b _ h => Fin.ext h)
      _ = d := Finset.card_range d
  exact Finset.eq_of_subset_of_card_le hsub hcard
