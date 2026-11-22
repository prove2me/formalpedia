-- Prove2me | solution 1 for UlmsTheorem.hillInvariant_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:05.638797+00:00
-- url     : https://prove2.me/submissions/bf1617e1-44d2-4edf-9744-a4a181239f02

module
public import Mathlib.Algebra.Field.ZMod
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Socle
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
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
open Ordinal Cardinal
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution (α : Ordinal) :
    hillInvariant p (⊥ : AddSubgroup G) α = ulmInvariant p α (G := G) := by
  have hden :
      hillSubmodule p (⊥ : AddSubgroup G) α = ulmDenSubmodule p α := by
    ext x
    change
      ((x : G) ∈ pSocleAt p α ⊓
        ((⊥ : AddSubgroup G) ⊔ ulmSubgroup p (Order.succ α))) ↔
      (x : G) ∈ pSocleAt p (Order.succ α)
    simp only [bot_sup_eq, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨_, hxSucc⟩
      exact (mem_pSocleAt p (Order.succ α) (x : G)).2
        ⟨(mem_pSocleAt p α (x : G)).1 x.property |>.1, hxSucc⟩
    · intro hx
      exact ⟨x.property, (mem_pSocleAt p (Order.succ α) (x : G)).1 hx |>.2⟩
  unfold hillInvariant ulmInvariant
  change Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ hillSubmodule p (⊥ : AddSubgroup G) α) =
    Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α)
  rw [hden]
end UlmsTheorem
