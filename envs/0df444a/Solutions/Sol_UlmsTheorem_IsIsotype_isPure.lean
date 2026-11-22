-- Prove2me | solution 1 for UlmsTheorem.IsIsotype.isPure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:55:28.335612+00:00
-- url     : https://prove2.me/submissions/8b0d1931-f135-4730-a774-fd5ee7e5ba92

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_nat


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
namespace IsIsotype
theorem _root_.solution {A : AddSubgroup G} (hA : IsIsotype p A) :
    IsPure p A := by
  intro n x hx
  rw [← ulmSubgroup_nat (p := p) (G := G) n] at hx
  rw [← ulmSubgroup_nat (p := p) (G := A) n]
  exact (hA x n).mp hx
end IsIsotype
end UlmsTheorem
