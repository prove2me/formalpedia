-- Prove2me | solution 1 for StabilityDichotomies.Solvability.dualHorn_greatest_solution
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:48:48.786429+00:00
-- url     : https://prove2.me/submissions/38135bfb-b7fb-48e3-b58d-4a12d610b6a1

import Definitions.Def_StabilityDichotomies_Solvability_Model
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem solution
    (Γ : Language)
    (hDualHorn : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i || y i) ∈ R.tuples)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I) :
    ∃ xmax : V → Bool, Solution I xmax ∧ ∀ x : V → Bool, Solution I x → x ≤ xmax := by
  have hjoin : ∀ x y : V → Bool, Solution I x → Solution I y → Solution I (x ⊔ y) := by
    intro x y hx hy c hc
    exact hDualHorn c.rel.val c.rel.property (fun i => x (c.scope i))
      (fun i => y (c.scope i)) (hx c hc) (hy c hc)
  let sols : Finset (V → Bool) := Finset.univ.filter (Solution I)
  have hSols : sols.Nonempty := by
    obtain ⟨x, hx⟩ := hSat
    exact ⟨x, by simp [sols, hx]⟩
  have hSup : ∀ S : Finset (V → Bool), S ⊆ sols → S.Nonempty → Solution I (S.sup id) := by
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
        simpa only [Finset.sup_insert, id_eq] using hjoin x (S.sup id) hx (ih hsSub hS)
      · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        simpa using hx
  refine ⟨sols.sup id, hSup sols (Finset.Subset.refl _) hSols, ?_⟩
  intro x hx
  exact Finset.le_sup (f := id) (s := sols) (by simpa [sols] using hx)

