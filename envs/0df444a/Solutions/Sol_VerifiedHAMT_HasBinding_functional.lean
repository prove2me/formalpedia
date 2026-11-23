-- Prove2me | solution 1 for VerifiedHAMT.HasBinding.functional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:18.313641+00:00
-- url     : https://prove2.me/submissions/dd1f67d8-6cef-40f0-a78f-c33a6bc85953

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_mkCollisionNode
public import Theorems.Thm_VerifiedHAMT_slot_zero
public import Theorems.Thm_VerifiedHAMT_valid_empty
public import Theorems.Thm_VerifiedHAMT_not_mem_empty
public import Theorems.Thm_VerifiedHAMT_hasBinding_collision
public import Theorems.Thm_VerifiedHAMT_hasBinding_entries
public import Theorems.Thm_VerifiedHAMT_HasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_EntryHasBinding_hasKey
public import Theorems.Thm_VerifiedHAMT_hasBinding_mkCollisionNode
attribute [local simp] VerifiedHAMT.hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_mkCollisionNode
attribute [local simp] VerifiedHAMT.slot_zero
attribute [local simp] VerifiedHAMT.valid_empty
attribute [local simp] VerifiedHAMT.not_mem_empty
attribute [local simp] VerifiedHAMT.hasBinding_collision
attribute [local simp] VerifiedHAMT.hasBinding_mkCollisionNode

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
namespace HasBinding
theorem _root_.solution {hashAt : α → USize} {node : Node α β}
    (wf : WellFormed hashAt node) (hu : Unique node) {key : α} {v w : β}
    (hv : HasBinding key v node) (hw : HasBinding key w node) : v = w := by
  induction wf generalizing v w with
  | collision hashAt keys vals hsz =>
    obtain ⟨i, hi, hki, hvi⟩ := hasBinding_collision.mp hv
    obtain ⟨j, hj, hkj, hwj⟩ := hasBinding_collision.mp hw
    have hij : i = j := by
      cases hu with | collision distinct => exact distinct i hi j hj (hki.trans hkj.symm)
    subst j
    exact hvi.symm.trans hwj
  | @entries hashAt es hs route children ih =>
    obtain ⟨i, hi, hvi⟩ := hasBinding_entries.mp hv
    obtain ⟨j, hj, hwj⟩ := hasBinding_entries.mp hw
    have hij : i = j := (route i hi key hvi.hasKey).symm.trans (route j hj key hwj.hasKey)
    subst j
    cases he : es[i] with
    | null => simp [he, EntryHasBinding] at hvi
    | entry k value =>
      have h1 : v = value := (show key = k ∧ v = value by simpa [he, EntryHasBinding] using hvi).2
      have h2 : w = value := (show key = k ∧ w = value by simpa [he, EntryHasBinding] using hwj).2
      exact h1.trans h2.symm
    | ref child =>
      have hc : Unique child := by cases hu with | entries hc => exact hc i hi child he
      exact ih i hi child he hc (by simpa [he, EntryHasBinding] using hvi)
        (by simpa [he, EntryHasBinding] using hwj)
end HasBinding
end VerifiedHAMT
