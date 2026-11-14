-- Prove2me | solution 1 for StabilityDichotomies.Solvability.horn_thinning_nonisolated_height_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:35:54.832351+00:00
-- url     : https://prove2.me/submissions/7084b950-4e0e-4107-b715-8a68a85fd9ef

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
import Theorems.Thm_StabilityDichotomies_Solvability_horn_least_solution
import Theorems.Thm_StabilityDichotomies_Solvability_least_solution_false_outside_scopes
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


theorem solution (Γ : Language)
    (hHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (mask : Fin I.constraints.card → Bool) :
    (∑ v : V, if extremalSolution (thinnedInstance I mask) false v then (1 : ℝ) else 0) ≤
      ((I.constraints.toFinset.biUnion fun c => Finset.univ.image c.scope).card : ℝ) := by
  let T := thinnedInstance I mask
  let X := extremalSolution T false
  let U := I.constraints.toFinset.biUnion fun c => Finset.univ.image c.scope
  have ht : Satisfiable T := by
    obtain ⟨x,hx⟩ := hSat
    exact ⟨x, thinned_solution I mask x hx⟩
  have hex := horn_least_solution Γ hHorn V T ht
  have hX : Solution T X ∧ ∀ y, Solution T y → X ≤ y := by
    change Solution T (extremalSolution T false) ∧
      ∀ y, Solution T y → extremalSolution T false ≤ y
    simp only [extremalSolution, Bool.false_eq_true, ↓reduceIte, dif_pos hex]
    exact Classical.choose_spec hex
  have hout (v : V) (hv : v ∉ U) : X v = false := by
    apply least_solution_false_outside_scopes T X hX.1 hX.2 v
    intro c hc k hcv
    have hci : c ∈ I.constraints := thinned_member I mask c hc
    have hvU : v ∈ U := by
      apply Finset.mem_biUnion.mpr
      refine ⟨c, Multiset.mem_toFinset.mpr hci, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_univ _, hcv⟩
    exact hv hvU
  have hsub : Finset.univ.filter (fun v => X v = true) ⊆ U := by
    intro v hv
    have hvx : X v = true := (Finset.mem_filter.mp hv).2
    by_contra hnot
    have := hout v hnot
    simp_all
  change (∑ v : V, if X v then (1 : ℝ) else 0) ≤ (U.card : ℝ)
  rw [Finset.sum_boole]
  exact_mod_cast Finset.card_le_card hsub
