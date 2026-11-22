-- Prove2me | solution 1 for UlmsTheorem.ulmHeight_eq_of_mem_not_mem_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:03.925309+00:00
-- url     : https://prove2.me/submissions/78756173-b351-47f5-b4a5-4cbec1110b68

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_coe_le_ulmHeight_of_mem
public import Theorems.Thm_UlmsTheorem_ulmHeight_le_of_not_mem_succ

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution (x : G) (α : Ordinal.{0})
    (hx : x ∈ ulmSubgroup p α (G := G))
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    ulmHeight p x = (α : WithTop Ordinal.{0}) :=
  le_antisymm (ulmHeight_le_of_not_mem_succ p x α hxs) (coe_le_ulmHeight_of_mem p x α hx)
end UlmsTheorem
