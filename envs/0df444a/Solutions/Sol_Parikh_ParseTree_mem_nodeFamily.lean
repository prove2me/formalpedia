-- Prove2me | solution 1 for Parikh.ParseTree.mem_nodeFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:33.163863+00:00
-- url     : https://prove2.me/submissions/461dad55-8993-487a-b97b-61eb4e294dee

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport

set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.ParseTree
variable {T N : Type*}
namespace Parikh.ParseTree
theorem _root_.solution (r : ContextFreeRule T N) (family : Finset (ParseTree T N))
    (children : List (ParseTree T N)) (hlen : children.length = r.output.length)
    (hchildren : ∀ c ∈ children, c ∈ family) : node r children ∈ nodeFamily r family := by
  classical
  let f : Fin r.output.length → family := fun i =>
    ⟨children[i.val]'(by omega), hchildren _ (List.getElem_mem (by omega))⟩
  apply Finset.mem_image.mpr
  refine ⟨f, Finset.mem_univ _, ?_⟩
  congr 1
  apply List.ext_getElem <;> simp [f, hlen]
end Parikh.ParseTree
