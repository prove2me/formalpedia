-- Prove2me | solution 1 for UlmsTheorem.mem_ulmSubgroup_iff_le_ulmHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:18.019802+00:00
-- url     : https://prove2.me/submissions/149afe61-2f21-43ed-9b29-7dfff80727ee

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
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_of_le_ulmHeight

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
theorem _root_.solution (x : G) (γ : Ordinal.{0}) :
    x ∈ ulmSubgroup p γ (G := G) ↔ (γ : WithTop Ordinal.{0}) ≤ ulmHeight p x :=
  ⟨coe_le_ulmHeight_of_mem p x γ, mem_ulmSubgroup_of_le_ulmHeight p x γ⟩
end UlmsTheorem
