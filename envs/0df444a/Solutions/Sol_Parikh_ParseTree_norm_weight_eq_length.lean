-- Prove2me | solution 1 for Parikh.ParseTree.norm_weight_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:43.376807+00:00
-- url     : https://prove2.me/submissions/a382ba5d-213a-4cd2-875c-1bc7202ef623

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
namespace ParseTree
theorem _root_.solution {T N : Type*} [Fintype T] [DecidableEq T]
    (t : ParseTree T N) : norm t.weight = t.yield.length := by
  classical
  change (∑ a, t.yield.count a) = t.yield.length
  rw [← List.sum_toFinset_count_eq_length t.yield]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  exact List.count_eq_zero.mpr (fun h => ha (List.mem_toFinset.mpr h))
end ParseTree
end Parikh
