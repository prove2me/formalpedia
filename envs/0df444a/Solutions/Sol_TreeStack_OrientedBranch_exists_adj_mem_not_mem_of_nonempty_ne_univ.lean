-- Prove2me | solution 1 for TreeStack.OrientedBranch.exists_adj_mem_not_mem_of_nonempty_ne_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:31:25.825977+00:00
-- url     : https://prove2.me/submissions/8db97b01-aa86-4849-a81b-78519cf98c18

import Mathlib
import Definitions.Def_TreeStack_HeightSource
import Definitions.Def_TreeStack_Consolidation

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (S : Finset V)
    (hNonempty : S.Nonempty)
    (hProper : S ≠ (Finset.univ : Finset V)) :
    ∃ a b : V, a ∈ S ∧ b ∉ S ∧ T.graph.Adj a b := by
  classical
  rcases hNonempty with ⟨x, hx⟩
  have hOutside : ∃ y : V, y ∉ S := by
    by_contra hOutside
    apply hProper
    rw [Finset.eq_univ_iff_forall]
    intro y
    by_contra hy
    exact hOutside ⟨y, hy⟩
  rcases hOutside with ⟨y, hy⟩
  rcases T.isTree.connected x y with ⟨p⟩
  have hCross :
      ∀ {u v : V} (q : T.graph.Walk u v),
        u ∈ S → v ∉ S →
          ∃ a b : V, a ∈ S ∧ b ∉ S ∧ T.graph.Adj a b := by
    intro u v q hu hv
    induction q with
    | nil =>
        exact (hv hu).elim
    | @cons u w v hadj q ih =>
        by_cases hw : w ∈ S
        · exact ih hw hv
        · exact ⟨u, w, hu, hw, hadj⟩
  exact hCross p hx hy
end TreeStack.OrientedBranch
