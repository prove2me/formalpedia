-- Prove2me | solution 1 for Parikh.ParseTree.height_child_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:45.206407+00:00
-- url     : https://prove2.me/submissions/99e9d500-3da1-4cc2-85a4-5aeb1ba5e5b2

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
theorem _root_.solution (r : ContextFreeRule T N) (children : List (ParseTree T N))
    (c : ParseTree T N) (hc : c ∈ children) : c.height < (node r children).height := by
  have hm : c.height ∈ children.map height := List.mem_map_of_mem hc
  have hmax := List.le_max_of_mem hm
  rw [height.eq_3, List.foldl_max_eq_max (List.ne_nil_of_mem hm), Nat.zero_max]
  omega
end Parikh.ParseTree
