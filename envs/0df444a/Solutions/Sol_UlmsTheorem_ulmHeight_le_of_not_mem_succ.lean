-- Prove2me | solution 1 for UlmsTheorem.ulmHeight_le_of_not_mem_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:24.505445+00:00
-- url     : https://prove2.me/submissions/92d67a9e-0a15-4250-be19-5b1057c79658

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone


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
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    ulmHeight p x ≤ (α : WithTop Ordinal.{0}) :=
  iSup₂_le fun β hxβ ↦ WithTop.coe_le_coe.mpr (by
    by_contra hβα
    exact hxs (ulmSubgroup_antitone p (Order.succ_le_iff.mpr (lt_of_not_ge hβα)) hxβ))
end UlmsTheorem
