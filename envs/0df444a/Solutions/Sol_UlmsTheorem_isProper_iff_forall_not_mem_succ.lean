-- Prove2me | solution 1 for UlmsTheorem.isProper_iff_forall_not_mem_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:46.160554+00:00
-- url     : https://prove2.me/submissions/92a2e9cb-1f7c-4821-b194-01a9e9f74918

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
public import Theorems.Thm_UlmsTheorem_ulmHeight_eq_of_mem_not_mem_succ

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
theorem _root_.solution (S : AddSubgroup G) {x : G}
    {α : Ordinal.{0}} (hx : x ∈ ulmSubgroup p α (G := G))
    (hxs : x ∉ ulmSubgroup p (Order.succ α) (G := G)) :
    IsProper p S x ↔ ∀ c : S, x + (c : G) ∉ ulmSubgroup p (Order.succ α) (G := G) := by
  have hheight := ulmHeight_eq_of_mem_not_mem_succ p x α hx hxs
  constructor
  · exact fun hproper c hc ↦ absurd
      (((coe_le_ulmHeight_of_mem p _ _ hc).trans (hproper c)).trans_eq hheight)
      (not_le_of_gt (WithTop.coe_lt_coe.mpr (Order.lt_succ α)))
  · intro h c
    change ulmHeight p (x + (c : G)) ≤ ulmHeight p x
    rw [hheight]
    exact ulmHeight_le_of_not_mem_succ p (x + (c : G)) α (h c)
end UlmsTheorem
