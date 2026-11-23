-- Prove2me | solution 1 for Reduce.keyLE_sorted_mergeSort
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:08:36.762879+00:00
-- url     : https://prove2.me/submissions/24e5cb9c-9e77-4634-b5a1-ee28bae25ac4

import Definitions.Def_Bdd_Collect
import Mathlib.Data.Sum.Order
import Definitions.Def_Bdd_Reduce_State
import Theorems.Thm_Reduce_keyLE_total
import Theorems.Thm_Reduce_keyLE_trans

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution {m : Nat}
    (l : List ((RawPointer × RawPointer) × Fin m)) :
    (l.mergeSort (fun a b => leKeyPair a.1 b.1)).Pairwise (fun a b => KeyLE a.1 b.1) := by
  have htrans : ∀ (a b c : (RawPointer × RawPointer) × Fin m),
      leKeyPair a.1 b.1 → leKeyPair b.1 c.1 → leKeyPair a.1 c.1 :=
    fun a b c hab hbc => keyLE_trans (a := a.1) (b := b.1) (c := c.1) hab hbc
  have htotal : ∀ (a b : (RawPointer × RawPointer) × Fin m),
      leKeyPair a.1 b.1 || leKeyPair b.1 a.1 :=
    fun a b => by
      rcases keyLE_total a.1 b.1 with h | h
      · exact (Bool.or_eq_true _ _).mpr (Or.inl h)
      · exact (Bool.or_eq_true _ _).mpr (Or.inr h)
  exact (List.pairwise_mergeSort htrans htotal l).imp (fun h => h)
end Reduce
