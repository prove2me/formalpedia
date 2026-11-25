-- Prove2me | solution 1 for SCCThm8.mem_ite_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:32.819646+00:00
-- url     : https://prove2.me/submissions/f1807e8d-a250-40ea-9ac9-a03c6408fa04

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {α : Type*} [DecidableEq α] (c : Prop) [Decidable c] (x i : α)
    (A : Finset α) : i ∈ (if c then insert x A else A) ↔ (c ∧ i = x) ∨ i ∈ A := by
  split_ifs with h <;> simp [h]
end SCCThm8
