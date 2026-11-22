-- Prove2me | solution 1 for Parikh.ParseTree.card_nodeFamily_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:50:05.460358+00:00
-- url     : https://prove2.me/submissions/a5490365-c7dd-4e09-888e-e6f909031d23

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
theorem _root_.solution (r : ContextFreeRule T N) (family : Finset (ParseTree T N)) :
    (nodeFamily r family).card ≤ family.card ^ r.output.length := by
  classical
  exact (Finset.card_image_le).trans_eq (by simp)
end Parikh.ParseTree
