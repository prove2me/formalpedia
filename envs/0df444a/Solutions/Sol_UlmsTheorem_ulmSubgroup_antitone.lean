-- Prove2me | solution 1 for UlmsTheorem.ulmSubgroup_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:54:46.872496+00:00
-- url     : https://prove2.me/submissions/d6aa23cd-6b9b-4f46-8b61-76b26497ef95

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_add_one
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_limit
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_mem_pImage
attribute [local simp] UlmsTheorem.mem_pImage


attribute [local simp] UlmsTheorem.ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]
namespace UlmsTheorem
theorem _root_.solution : Antitone (fun α ↦ ulmSubgroup p α (G := G)) := by
  let P : Ordinal → Prop := fun β ↦ ∀ α, α ≤ β → ulmSubgroup p β (G := G) ≤ ulmSubgroup p α
  have hP : ∀ β, P β := by
    intro β
    induction β using Ordinal.limitRecOn with
    | zero =>
        intro α hαβ
        have h0 : α = 0 := le_antisymm hαβ bot_le
        simp [h0]
    | add_one β ih =>
        intro α hαβ
        have hs : ulmSubgroup p (β + 1) (G := G) ≤ ulmSubgroup p β := by
          rw [ulmSubgroup_add_one]
          intro x hx
          rcases hx with ⟨y, hy, rfl⟩
          simpa using (ulmSubgroup p β (G := G)).nsmul_mem hy p
        rcases lt_or_eq_of_le hαβ with hlt | rfl
        · exact hs.trans (ih α (Order.le_of_lt_succ hlt))
        · exact le_rfl
    | limit o ho IH =>
        intro α hαβ
        rcases lt_or_eq_of_le hαβ with hlt | rfl
        · rw [ulmSubgroup_limit p o ho]
          exact iInf_le_of_le α (iInf_le _ hlt)
        · exact le_rfl
  intro α β hαβ
  exact hP β α hαβ
end UlmsTheorem
