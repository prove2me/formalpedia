-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.containsNode_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:46:10.675266+00:00
-- url     : https://prove2.me/submissions/2c022c4d-db45-47d9-9de8-35219d316375

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_entries
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
public import Theorems.Thm_VerifiedHAMT_hasKey_entries


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α} (wf : WellFormed hashAt node) (key : α)
    (member : HasKey key node) : containsNode node (hashAt key) key = true := by
  induction wf with
  | collision hashAt keys =>
    simpa [containsNode] using (hasKey_collision.mp member)
  | @entries hashAt es size_eq routing children ih =>
    obtain ⟨i, hi, hkey⟩ := hasKey_entries.mp member
    have hslot := routing i hi key hkey
    subst i
    rw [containsNode, dif_pos hi]
    cases he : es[slot (hashAt key)] <;> simp [EntryHasKey] at * <;> grind
end VerifiedHAMT.SetWithoutValArray.Raw
