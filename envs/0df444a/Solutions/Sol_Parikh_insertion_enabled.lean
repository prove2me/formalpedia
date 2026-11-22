-- Prove2me | solution 1 for Parikh.insertion_enabled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:01.552863+00:00
-- url     : https://prove2.me/submissions/e834e3da-e91e-4b65-8219-a5bbd0510725

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Theorems.Thm_Parikh_plugging
public import Theorems.Thm_Parikh_Complete_mem_support_iff_subtree
public import Theorems.Thm_Parikh_Complete_subtree_context


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T) (t C : ParseTree T g.NT)
    (A : g.NT) (ht : Complete g t) (hC : Cycle g C A) :
    (∃ t', Inserts g t C t') ↔ A ∈ t.support := by
  classical
  constructor
  · rintro ⟨t', _, _, B, hCB, q, u, hpos, hu, _⟩
    have hBA : B = A := Symbol.nonterminal.inj (hCB.2.1.symm.trans hC.2.1)
    subst B
    exact (ht.mem_support_iff_subtree A).mpr ⟨q, u, hpos, hu⟩
  · intro hA
    obtain ⟨q, u, hpos, hu⟩ := (ht.mem_support_iff_subtree A).mp hA
    obtain ⟨huc, E, hE, _, _, hreplace⟩ := ht.subtree_context q u hpos A hu
    have hCu := plugging g C u A hC.1 huc hu
    have hCuRoot : (C.plug u).root = .nonterminal A := hCu.2.1.trans hC.2.1
    have hwhole := plugging g E (C.plug u) A hE hCu.1 hCuRoot
    exact ⟨E.plug (C.plug u), ht, hwhole.1, A, hC, q, u, hpos, hu,
      hreplace (C.plug u)⟩
end Parikh
