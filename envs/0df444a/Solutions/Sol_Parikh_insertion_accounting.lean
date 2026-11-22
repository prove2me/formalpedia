-- Prove2me | solution 1 for Parikh.insertion_accounting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:08.748799+00:00
-- url     : https://prove2.me/submissions/f1fd5ed8-12a4-4437-8aee-c6bff1fa6e02

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Theorems.Thm_Parikh_plugging
public import Theorems.Thm_Parikh_Complete_subtree_context


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}
namespace Parikh
theorem _root_.solution [DecidableEq T] (g : ContextFreeGrammar T)
    (t C t' : ParseTree T g.NT) (h : Inserts g t C t') :
    t'.root = t.root ∧ t'.weight = t.weight + C.weight ∧
      t'.productionSize = t.productionSize + C.productionSize ∧
      t'.support = t.support ∪ C.support := by
  obtain ⟨ht, _, A, hC, q, u, hpos, hu, hreplace⟩ := h
  obtain ⟨huc, E, hE, hroot, hplug, houter⟩ := ht.subtree_context q u hpos A hu
  have hCu := plugging g C u A hC.1 huc hu
  have hCuRoot : (C.plug u).root = .nonterminal A := hCu.2.1.trans hC.2.1
  have hbefore := plugging g E u A hE huc hu
  have hafter := plugging g E (C.plug u) A hE hCu.1 hCuRoot
  have hresult : E.plug (C.plug u) = t' :=
    Option.some.inj ((houter (C.plug u)).symm.trans hreplace)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hresult, hafter.2.1, hroot]
  · rw [← hresult, hafter.2.2.1, hCu.2.2.1, ← hplug, hbefore.2.2.1]
    ac_rfl
  · rw [← hresult, hafter.2.2.2.1, hCu.2.2.2.1, ← hplug, hbefore.2.2.2.1]
    omega
  · rw [← hresult, hafter.2.2.2.2, hCu.2.2.2.2, ← hplug, hbefore.2.2.2.2]
    ext B
    simp only [Set.mem_union]
    tauto
end Parikh
