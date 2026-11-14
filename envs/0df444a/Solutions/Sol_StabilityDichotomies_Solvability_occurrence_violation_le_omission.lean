-- Prove2me | solution 1 for StabilityDichotomies.Solvability.occurrence_violation_le_omission
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:46:57.527205+00:00
-- url     : https://prove2.me/submissions/3ef01dfe-31f0-4e39-b2f6-ea704a285e24

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
import Theorems.Thm_StabilityDichotomies_Solvability_horn_least_solution
import Theorems.Thm_StabilityDichotomies_Solvability_dualHorn_greatest_solution
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory
namespace StabilityDichotomies.Solvability

private theorem thinned_member {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (c : Constraint Γ V)
    (hc : c ∈ (thinnedInstance I mask).constraints) : c ∈ I.constraints := by
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter,
    List.mem_ofFn] at hc
  obtain ⟨⟨i, d⟩, ⟨⟨j, hj⟩, hm⟩, hd⟩ := hc
  cases hj
  simp only [Prod.snd] at hd
  subst c
  simp only [occurrenceAt]
  exact Multiset.mem_toList.mp (List.get_mem _ _)

private theorem thinned_solution {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (x : V → Bool)
    (hx : Solution I x) : Solution (thinnedInstance I mask) x := by
  intro c hc
  exact hx c (thinned_member I mask c hc)

private theorem thinned_extremal_solution (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (mask : Fin I.constraints.card → Bool) :
    Solution (thinnedInstance I mask) (extremalSolution (thinnedInstance I mask) b) := by
  have ht : Satisfiable (thinnedInstance I mask) := by
    obtain ⟨x, hx⟩ := hSat
    exact ⟨x, thinned_solution I mask x hx⟩
  have he : ∃ x : V → Bool, Solution (thinnedInstance I mask) x ∧
      ∀ y : V → Bool, Solution (thinnedInstance I mask) y → (if b then y ≤ x else x ≤ y) := by
    cases b with
    | false =>
      simpa using horn_least_solution Γ (by simpa using hΓ) V (thinnedInstance I mask) ht
    | true =>
      simpa using dualHorn_greatest_solution Γ (by simpa using hΓ) V (thinnedInstance I mask) ht
  simp only [extremalSolution, dif_pos he]
  exact (Classical.choose_spec he).1

private theorem occurrence_retained {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (i : Fin I.constraints.card)
    (hi : mask i = true) : occurrenceAt I i ∈ (thinnedInstance I mask).constraints := by
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_ofFn]
  exact ⟨(i, occurrenceAt I i), ⟨⟨i,rfl⟩,hi⟩,rfl⟩

end StabilityDichotomies.Solvability
open StabilityDichotomies.Solvability

theorem solution (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (i : Fin I.constraints.card) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
      (if (occurrenceAt I i).Satisfied (extremalSolution (thinnedInstance I mask) b) then 0 else 1)) ≤
    (∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask * (if mask i then 0 else 1)) := by
  apply Finset.sum_le_sum
  intro mask hm
  have hw : 0 ≤ retentionWeight p mask := by
    unfold retentionWeight
    apply Finset.prod_nonneg
    intro j hj
    split_ifs <;> linarith
  by_cases hi : mask i = true
  · have hs : (occurrenceAt I i).Satisfied (extremalSolution (thinnedInstance I mask) b) :=
      thinned_extremal_solution Γ b hΓ V I hSat mask _ (occurrence_retained I mask i hi)
    simp [hi, hs]
  · have hf : mask i = false := by cases h : mask i <;> simp_all
    simp [hf]
    split_ifs <;> linarith
