-- Prove2me | solution 1 for Parikh.ParseTree.exists_root_mem_child_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:25.354797+00:00
-- url     : https://prove2.me/submissions/d08e3bfe-e670-4132-8a1c-957b220e3afa

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Theorems.Thm_Parikh_ParseTree_labelPath_subset_support


set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree
namespace Parikh.ParseTree
theorem _root_.solution (r : ContextFreeRule T N)
    (cs : List (ParseTree T N)) (hs : ¬ (node r cs).Simple)
    (hc : ∀ c ∈ cs, c.Simple) : ∃ c ∈ cs, r.input ∈ c.support := by
  by_contra h
  apply hs
  intro path hp
  simp only [labelPaths, List.mem_cons, List.mem_map, ← List.flatMap_def,
    List.mem_flatMap] at hp
  rcases hp with rfl | ⟨tail, ⟨c, hcmem, htail⟩, rfl⟩
  · simp
  · apply List.nodup_cons.mpr
    refine ⟨?_, hc c hcmem tail htail⟩
    intro hA
    exact h ⟨c, hcmem, c.labelPath_subset_support tail htail r.input hA⟩
end Parikh.ParseTree
