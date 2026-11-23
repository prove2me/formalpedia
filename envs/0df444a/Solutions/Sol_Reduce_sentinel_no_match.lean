-- Prove2me | solution 1 for Reduce.sentinel_no_match
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:13:18.419362+00:00
-- url     : https://prove2.me/submissions/1ea1e709-32e7-4688-bad6-c68d254a24d1

import Definitions.Def_Bdd_Reduce_Populate
import Definitions.Def_Bdd_Reduce_Process

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded Subrelation
open Pointer
open Bdd
open RawBdd
open Reduce
namespace Reduce
theorem _root_.solution
    (Q : List ((RawPointer × RawPointer) × Fin m))
    (hnonred : ∀ entry ∈ Q, entry.1.1 ≠ entry.1.2) :
    ∀ entry ∈ Q, entry.1 ≠ ((.inl false : RawPointer), (.inl false : RawPointer)) := by
  intro entry hmem heq
  have h := hnonred entry hmem
  have : entry.1.1 = entry.1.2 := by
    have h1 : entry.1.1 = .inl false := congrArg Prod.fst heq
    have h2 : entry.1.2 = .inl false := congrArg Prod.snd heq
    rw [h1, h2]
  exact h this
end Reduce
