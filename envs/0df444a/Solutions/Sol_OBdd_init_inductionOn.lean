-- Prove2me | solution 1 for OBdd.init_inductionOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:03:02.139812+00:00
-- url     : https://prove2.me/submissions/c135c83f-cf2b-4c5a-ac53-99b15f99baef

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Bdd_terminal_or_node
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution t {motive : OBdd n m → Prop}
    (base : (b : Bool) → motive ⟨{heap := t.1.heap, root := terminal b}, Ordered_of_terminal⟩)
    (step : (j : Fin m) →
            (hl : ({heap := t.1.heap, root := t.1.heap[j].low} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := t.1.heap[j].low}, hl⟩ →
            (hh : ({heap := t.1.heap, root := t.1.heap[j].high} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := t.1.heap[j].high}, hh⟩ →
            (h : ({heap := t.1.heap, root := node j} : Bdd n m).Ordered) →
            motive ⟨{heap := t.1.heap, root := node j}, h⟩)
    : motive t := by
  rcases (terminal_or_node t.1) with ⟨b, h1, h2⟩ | ⟨j, h1, h2⟩
  case inl => convert base b using 2; apply Subtype.ext_iff.mpr; assumption
  case inr =>
    convert step j _ _ _ _ _ using 2
    · apply Subtype.ext_iff.mpr; assumption; exact ordered_of_relevant t ⟨node j, by simp only [Reachable]; rw [← h1]⟩
    · exact ordered_of_relevant t ⟨t.1.heap[j].low, by rw [h1]; exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Edge.low rfl)⟩
    · exact solution _ base step
    · exact ordered_of_relevant t ⟨t.1.heap[j].high, by rw [h1]; exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Edge.high rfl)⟩
    · exact solution _ base step
termination_by t
decreasing_by
  · constructor
    · simp
    · convert Edge.low rfl
  · simp only [flip, Ordered, Fin.getElem_fin, OEdge, true_and]; convert Edge.high rfl <;> rfl
end OBdd
