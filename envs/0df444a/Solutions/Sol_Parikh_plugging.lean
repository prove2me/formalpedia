-- Prove2me | solution 1 for Parikh.plugging
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:08.549795+00:00
-- url     : https://prove2.me/submissions/bdf097d3-595c-4fe2-b22d-91ff3f6f3fe1

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Theorems.Thm_Parikh_ParseTree_count_yield_plug
public import Theorems.Thm_Parikh_ParseTree_mem_support_plug
public import Theorems.Thm_Parikh_ParseTree_productionSize_plug
public import Theorems.Thm_Parikh_Valid_plug_complete


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (g : ContextFreeGrammar T) (E t : ParseTree T g.NT)
    (A : g.NT) (hE : OneHole g E A) (ht : Complete g t)
    (hroot : t.root = .nonterminal A) :
    Complete g (E.plug t) ∧ (E.plug t).root = E.root ∧
      (E.plug t).weight = E.weight + t.weight ∧
      (E.plug t).productionSize = E.productionSize + t.productionSize ∧
      (E.plug t).support = E.support ∪ t.support := by
  obtain ⟨hvalid, hholes⟩ := hE
  have hsemantics := hvalid.plug_complete ht (by
    intro B hB
    have hBA : B = A := by simpa only [hholes, List.mem_singleton] using hB
    simpa only [hBA] using hroot)
  refine ⟨hsemantics.1, hsemantics.2, ?_, ?_, ?_⟩
  · funext a
    simpa only [ParseTree.weight, counts, Pi.add_apply, hholes,
      List.length_singleton, Nat.one_mul] using E.count_yield_plug t a
  · simpa only [hholes, List.length_singleton, Nat.one_mul]
      using E.productionSize_plug t
  · ext B
    simp [E.mem_support_plug t B, hholes]
end Parikh
