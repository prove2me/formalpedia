-- Prove2me | solution 1 for StabilityDichotomies.Solvability.horn_least_solution
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:48:48.132045+00:00
-- url     : https://prove2.me/submissions/a8998ed7-06fd-4698-9228-15901513c8b4

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem solution
    (Γ : Language)
    (hHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I) :
    ∃ xmin : V → Bool, Solution I xmin ∧ ∀ x : V → Bool, Solution I x → xmin ≤ x := by
  have hmeet : ∀ x y : V → Bool, Solution I x → Solution I y → Solution I (x ⊓ y) := by
    intro x y hx hy c hc
    exact hHorn c.rel.val c.rel.property (fun i => x (c.scope i))
      (fun i => y (c.scope i)) (hx c hc) (hy c hc)
  let sols : Finset (V → Bool) := Finset.univ.filter (Solution I)
  have hSols : sols.Nonempty := by
    obtain ⟨x, hx⟩ := hSat
    exact ⟨x, by simp [sols, hx]⟩
  have hInf : ∀ S : Finset (V → Bool), S ⊆ sols → S.Nonempty → Solution I (S.inf id) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert x S hxS ih =>
      intro hsub hne
      have hx : Solution I x := by
        have : x ∈ sols := hsub (Finset.mem_insert_self x S)
        simpa [sols] using this
      by_cases hS : S.Nonempty
      · have hsSub : S ⊆ sols := by
          intro y hy
          exact hsub (Finset.mem_insert_of_mem hy)
        simpa only [Finset.inf_insert, id_eq] using hmeet x (S.inf id) hx (ih hsSub hS)
      · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        simpa using hx
  refine ⟨sols.inf id, hInf sols (Finset.Subset.refl _) hSols, ?_⟩
  intro x hx
  exact Finset.inf_le (by simpa [sols] using hx)

