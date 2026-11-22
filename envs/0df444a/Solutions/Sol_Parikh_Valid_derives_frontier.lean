-- Prove2me | solution 1 for Parikh.Valid.derives_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:16.818507+00:00
-- url     : https://prove2.me/submissions/758533f0-a62f-4723-bbf8-cbe8a3346f77

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
variable {N : Type*}
namespace Parikh
namespace Valid
theorem _root_.solution {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) : g.Derives [t.root] t.frontier := by
  induction ht with
  | terminal a => simpa only [ParseTree.root, ParseTree.frontier] using
      (ContextFreeGrammar.Derives.refl (g := g) [.terminal a])
  | hole A => simpa only [ParseTree.root, ParseTree.frontier] using
      (ContextFreeGrammar.Derives.refl (g := g) [.nonterminal A])
  | node r children hr hc roots ih =>
    have forest : g.Derives (children.map ParseTree.root)
        (children.map ParseTree.frontier).flatten := by
      clear hc roots
      induction children with
      | nil => exact .refl _
      | cons c cs hcs =>
        have hhead := ih c (by simp)
        have htail := hcs (fun t ht => ih t (by simp [ht]))
        exact (hhead.append_right (cs.map ParseTree.root)).trans
          (htail.append_left c.frontier)
    simpa only [ParseTree.root, ParseTree.frontier] using
      (ContextFreeGrammar.Produces.single (g := g) ⟨r, hr,
        ContextFreeRule.Rewrites.input_output⟩).trans (roots ▸ forest)
end Valid
end Parikh
