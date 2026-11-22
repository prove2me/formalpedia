-- Prove2me | solution 1 for UlmsTheorem.ulmHeight_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:34.556864+00:00
-- url     : https://prove2.me/submissions/08d3b5e5-d28d-4347-8299-379e6f2e1d99

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_ulmHeight_le_of_mem_imp
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_zsmul_iff

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
theorem _root_.solution [Fact p.Prime] (hprim : IsPrimaryPGroup p G)
    {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (u : G) :
    ulmHeight p (n • u) = ulmHeight p u := by
  apply le_antisymm
  · exact ulmHeight_le_of_mem_imp p _ _
      (fun γ h ↦ (mem_ulmSubgroup_zsmul_iff p hprim hn u γ).mp h)
  · exact ulmHeight_le_of_mem_imp p _ _
      (fun γ h ↦ (mem_ulmSubgroup_zsmul_iff p hprim hn u γ).mpr h)
end UlmsTheorem
