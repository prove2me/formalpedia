-- Prove2me | solution 1 for UlmsTheorem.ulmHeight_subgroup_le_ambient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:28.329176+00:00
-- url     : https://prove2.me/submissions/3c9ab179-3405-4f25-a126-e498397a2327

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_map_ulmSubgroup_le


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
theorem _root_.solution {A : AddSubgroup G} (x : A) :
    ulmHeight p x (G := A) ≤ ulmHeight p (x : G) :=
  iSup₂_le fun α hx ↦ le_iSup_of_le α <| le_iSup_of_le
    (map_ulmSubgroup_le (p := p) (φ := A.subtype) α ⟨x, hx, rfl⟩) le_rfl
end UlmsTheorem
