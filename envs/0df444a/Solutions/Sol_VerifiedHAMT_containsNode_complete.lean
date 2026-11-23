-- Prove2me | solution 1 for VerifiedHAMT.containsNode_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:07.623632+00:00
-- url     : https://prove2.me/submissions/deb219dc-3f9d-4744-ad6b-ed1bebaa2bd5

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α)
    (member : HasKey key node) : containsNode node (hashAt key) key = true := by
  induction wf with
  | collision hashAt keys vals hsz =>
    simpa [containsNode] using (hasKey_collision.mp member)
  | @entries hashAt es size_eq routing children ih =>
    obtain ⟨i, hi, hkey⟩ := hasKey_entries.mp member
    have hslot := routing i hi key hkey
    subst i
    rw [containsNode, dif_pos hi]
    cases he : es[slot (hashAt key)] <;> simp [EntryHasKey] at * <;> grind
end VerifiedHAMT
