-- Prove2me | solution 1 for Parikh.Valid.support_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:21.199305+00:00
-- url     : https://prove2.me/submissions/4163f827-f530-4d10-a7cc-c0ba3906e919

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_Parikh_GrammarTrees

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
namespace Valid
theorem _root_.solution {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) : t.support ⊆ (activeNonterminals g : Set g.NT) := by
  classical
  induction ht with
  | terminal a =>
    intro A hA
    change A ∈ (ParseTree.terminal a : ParseTree T g.NT).productionLabels at hA
    rw [ParseTree.productionLabels.eq_1] at hA
    exact False.elim (List.not_mem_nil hA)
  | hole A =>
    intro B hB
    change B ∈ (ParseTree.hole A : ParseTree T g.NT).productionLabels at hB
    rw [ParseTree.productionLabels.eq_2] at hB
    exact False.elim (List.not_mem_nil hB)
  | node r children hr hc roots ih =>
    intro A hA
    change A ∈ (ParseTree.node r children).productionLabels at hA
    rw [ParseTree.productionLabels.eq_3] at hA
    rcases List.mem_cons.mp hA with rfl | hA
    · unfold activeNonterminals
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨r, hr, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
    · obtain ⟨labels, hlabels, hA⟩ := List.mem_flatten.mp hA
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hlabels
      exact ih c hc hA
end Valid
end Parikh
