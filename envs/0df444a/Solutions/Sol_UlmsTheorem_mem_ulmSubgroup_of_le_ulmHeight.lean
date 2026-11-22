-- Prove2me | solution 1 for UlmsTheorem.mem_ulmSubgroup_of_le_ulmHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:52.773503+00:00
-- url     : https://prove2.me/submissions/54f9a7b9-2261-427c-aef7-bccce7e8ed0b

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_ulmHeight_le_of_not_mem_succ
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_limit_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



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
theorem _root_.solution (x : G) (γ : Ordinal.{0})
    (h : (γ : WithTop Ordinal.{0}) ≤ ulmHeight p x) :
    x ∈ ulmSubgroup p γ (G := G) := by
  induction γ using Ordinal.limitRecOn with
  | zero => simp
  | add_one δ _ih =>
      by_contra hx
      have hle : ulmHeight p x ≤ (δ : WithTop Ordinal.{0}) :=
        ulmHeight_le_of_not_mem_succ p x δ hx
      have : ((Order.succ δ : Ordinal.{0}) : WithTop Ordinal.{0})
          ≤ (δ : WithTop Ordinal.{0}) := le_trans h hle
      exact absurd (WithTop.coe_le_coe.mp this) (not_le_of_gt (Order.lt_succ δ))
  | limit δ hlim ih =>
      rw [mem_ulmSubgroup_limit_iff (p := p) (G := G) hlim]
      intro β hβ
      refine ih β hβ (le_trans ?_ h)
      exact WithTop.coe_le_coe.mpr (le_of_lt hβ)
end UlmsTheorem
