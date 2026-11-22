-- Prove2me | solution 1 for UlmsTheorem.ulmHeight_le_of_mem_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:13.485074+00:00
-- url     : https://prove2.me/submissions/bd76fbd8-5c12-4def-a33d-9fbc12feb128

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
theorem _root_.solution (x y : G)
    (h : ∀ α : Ordinal.{0},
      x ∈ ulmSubgroup p α (G := G) → y ∈ ulmSubgroup p α (G := G)) :
    ulmHeight p x ≤ ulmHeight p y :=
  iSup₂_le fun α hx ↦ le_iSup_of_le α (le_iSup_of_le (h α hx) le_rfl)
end UlmsTheorem
