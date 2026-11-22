-- Prove2me | solution 1 for UlmsTheorem.coe_le_ulmHeight_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:13.065277+00:00
-- url     : https://prove2.me/submissions/b4aa8639-b89d-456f-a8d6-9581a194cd07

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure

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
    (hx : x ∈ ulmSubgroup p α (G := G)) :
    (α : WithTop Ordinal.{0}) ≤ ulmHeight p x :=
  le_iSup_of_le α (le_iSup_of_le hx le_rfl)
end UlmsTheorem
