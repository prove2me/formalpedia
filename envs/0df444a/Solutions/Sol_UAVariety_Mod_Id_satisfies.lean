-- Prove2me | solution 1 for UAVariety.Mod_Id_satisfies
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:47:05.860371+00:00
-- url     : https://prove2.me/submissions/3885f15c-d862-4e49-9ec5-242c10567bf3

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem bh_realize_congr {X M : Type*} [L.Structure M] [DecidableEq X] (t : L.Term X) (v w : X → M)
    (h : ∀ x ∈ t.varFinset, v x = w x) : t.realize v = t.realize w := by
  induction t with
  | var x => exact h x (by simp [Term.varFinset])
  | func f ts ih =>
    simp only [Term.realize]
    congr 1
    funext i
    exact ih i (fun x hx => h x (by
      simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hx⟩))

theorem bh_satisfies_of_Id (K : Set (Alg L)) {X : Type*} (p q : L.Term X)
    (hK : ∀ B ∈ K, Satisfies B (p, q)) (A : Alg L) (hA : A ∈ Mod (Id K)) :
    Satisfies A (p, q) := by
  classical
  intro v
  rcases isEmpty_or_nonempty A with hE | ⟨⟨a₀⟩⟩
  · exact (hE.false (p.realize v)).elim
  let s := p.varFinset ∪ q.varFinset
  let e := s.equivFin
  let g : X → ℕ := fun x => if hx : x ∈ s then ((e ⟨x, hx⟩ : Fin s.card) : ℕ) else 0
  let w : ℕ → A := fun n => if hn : n < s.card then v (e.symm ⟨n, hn⟩) else a₀
  have hgw : ∀ x ∈ s, w (g x) = v x := by
    intro x hx
    have hlt : ((e ⟨x, hx⟩ : Fin s.card) : ℕ) < s.card := (e ⟨x, hx⟩).isLt
    simp only [w, g, dif_pos hx, dif_pos hlt, Fin.eta, Equiv.symm_apply_apply]
  have hId : (p.relabel g, q.relabel g) ∈ Id K := by
    intro B hB u
    show (p.relabel g).realize u = (q.relabel g).realize u
    rw [Term.realize_relabel, Term.realize_relabel]
    exact hK B hB (u ∘ g)
  have h1 : (p.relabel g).realize w = (q.relabel g).realize w := hA _ hId w
  rw [Term.realize_relabel, Term.realize_relabel] at h1
  have ep : p.realize (w ∘ g) = p.realize v :=
    bh_realize_congr p _ _ (fun x hx => hgw x (Finset.mem_union_left _ hx))
  have eq : q.realize (w ∘ g) = q.realize v :=
    bh_realize_congr q _ _ (fun x hx => hgw x (Finset.mem_union_right _ hx))
  exact ep.symm.trans (h1.trans eq)

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (UAVariety.Alg L)) {X : Type*} (p q : L.Term X)
    (hK : ∀ B ∈ K, UAVariety.Satisfies B (p, q)) (A : UAVariety.Alg L) (hA : A ∈ UAVariety.Mod (UAVariety.Id K)) :
    UAVariety.Satisfies A (p, q) :=
  UAVariety.bh_satisfies_of_Id K p q hK A hA
