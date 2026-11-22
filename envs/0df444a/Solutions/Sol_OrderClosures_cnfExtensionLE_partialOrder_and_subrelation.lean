-- Prove2me | solution 1 for OrderClosures.cnfExtensionLE_partialOrder_and_subrelation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:15.296911+00:00
-- url     : https://prove2.me/submissions/afad8e76-54ff-4707-8849-14abc5e64b85

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Theorems.Thm_OrderClosures_CNFListLT_ordinal_lt
public import Theorems.Thm_OrderClosures_cnfExtensionLT_iff_CNFListLT
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderConvergesTo_le


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution :
    IsPartialOrder (Ordinal.{u}) cnfExtensionLE ∧
      ∀ {ζ ζ' : Ordinal.{u}}, cnfExtensionLE ζ ζ' → ζ ≤ ζ' := by
  have hlt : ∀ {ζ ζ' : Ordinal.{u}}, cnfExtensionLT ζ ζ' → ζ < ζ' := by
    intro ζ ζ' h
    exact CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp h)
  have htrans : ∀ a b c : Ordinal.{u}, cnfExtensionLT a b →
      cnfExtensionLT b c → cnfExtensionLT a c := by
    intro a b c hab hbc
    apply cnfExtensionLT_iff_CNFListLT.mpr
    exact CNFListLT.trans (cnfExtensionLT_iff_CNFListLT.mp hab)
      (cnfExtensionLT_iff_CNFListLT.mp hbc)
  let : IsPreorder (Ordinal.{u}) cnfExtensionLE := {
    refl := fun _ ↦ Or.inl rfl
    trans := fun a b c hab hbc ↦ by
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr (htrans a b c hab hbc)
    }
  let : Std.Antisymm
      (cnfExtensionLE : Ordinal.{u} → Ordinal.{u} → Prop) := ⟨by
    intro a b hab hba
    rcases hab with rfl | hab
    · rfl
    rcases hba with rfl | hba
    · rfl
    · exact ((hlt hab).asymm (hlt hba)).elim
    ⟩
  constructor
  · exact IsPartialOrder.mk
  · intro ζ ζ' h
    rcases h with rfl | h
    · exact le_rfl
    · exact (hlt h).le
end OrderClosures
