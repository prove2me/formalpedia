-- Prove2me | solution 1 for UlmsTheorem.IsHeightPreserving.injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:56:56.931913+00:00
-- url     : https://prove2.me/submissions/e0ac9c3d-e89e-44cd-a3a2-6b5d480855c9

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


attribute [local simp] UlmsTheorem.pOrder_zero

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
namespace IsHeightPreserving
theorem _root_.solution (hred : IsPReduced p G)
    {φ : G →+ H} (hφ : IsHeightPreserving p φ) :
    Function.Injective φ := by
  intro x y hxy
  rcases hred with ⟨α, hα⟩
  have hmem : x - y ∈ ulmSubgroup p α (G := G) :=
    (hφ (x - y) α).mpr (by simp [hxy])
  rw [hα] at hmem
  exact sub_eq_zero.mp (AddSubgroup.mem_bot.mp hmem)
end IsHeightPreserving
end UlmsTheorem
