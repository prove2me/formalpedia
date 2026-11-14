-- Prove2me | solution 1 for StabilityDichotomies.Solvability.thinned_extremal_solution
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:42:47.847194+00:00
-- url     : https://prove2.me/submissions/ffb446d7-b02a-4389-8ed5-3157711a0056

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

end StabilityDichotomies.Solvability
open StabilityDichotomies.Solvability

theorem solution (Γ : Language) (b : Bool)
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
