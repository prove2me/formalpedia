-- Prove2me | solution 1 for UlmsTheorem.IsIsotype.ulmHeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:31.089834+00:00
-- url     : https://prove2.me/submissions/b26c4cf4-a3e2-4d41-ad1f-6354e5f1285c

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
namespace IsIsotype
theorem _root_.solution {A : AddSubgroup G} (hA : IsIsotype p A) (x : A) :
    ulmHeight p (x : G) = ulmHeight p x (G := A) :=
  le_antisymm
    (iSup₂_le fun α hx ↦ le_iSup_of_le α <| le_iSup_of_le ((hA x α).mp hx) le_rfl)
    (iSup₂_le fun α hx ↦ le_iSup_of_le α <| le_iSup_of_le ((hA x α).mpr hx) le_rfl)
end IsIsotype
end UlmsTheorem
