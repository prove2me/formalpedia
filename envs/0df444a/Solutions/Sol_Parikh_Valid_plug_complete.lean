-- Prove2me | solution 1 for Parikh.Valid.plug_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:48.039837+00:00
-- url     : https://prove2.me/submissions/af7fecfa-911c-4785-b71a-2dff7a5f2818

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_TreePlugging

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
namespace Parikh
namespace Valid
theorem _root_.solution {g : ContextFreeGrammar T} {E t : ParseTree T g.NT}
    (hE : Valid g E) (ht : Complete g t)
    (hmatch : ∀ A ∈ E.holes, t.root = .nonterminal A) :
    Complete g (E.plug t) ∧ (E.plug t).root = E.root := by
  induction hE with
  | terminal a =>
    simp only [ParseTree.plug, Complete, ParseTree.holes]
    exact ⟨⟨.terminal a, True.intro⟩, True.intro⟩
  | hole A =>
    simpa only [ParseTree.plug, ParseTree.root] using
      And.intro ht (hmatch A (by simp [ParseTree.holes]))
  | node r children hr hc roots ih =>
    have children_plug : ∀ c ∈ children,
        Complete g (c.plug t) ∧ (c.plug t).root = c.root := by
      intro c hcmem
      apply ih c hcmem
      intro A hA
      apply hmatch A
      simp only [ParseTree.holes, ← List.flatMap_def, List.mem_flatMap]
      exact ⟨c, hcmem, hA⟩
    refine ⟨⟨?_, ?_⟩, by simp [ParseTree.plug, ParseTree.root]⟩
    · simp only [ParseTree.plug]
      refine Valid.node r _ hr ?_ ?_
      · intro c hc
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        exact (children_plug d hd).1.1
      · rw [List.map_map, ← roots]
        exact List.map_congr_left fun c hc => (children_plug c hc).2
    · simp only [ParseTree.plug, ParseTree.holes, List.flatten_eq_nil_iff,
        List.forall_mem_map]
      intro c hc
      exact (children_plug c hc).1.2
end Valid
end Parikh
