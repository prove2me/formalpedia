-- Prove2me | solution 1 for VerifiedHAMT.containsThenInsert_eq_impl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:18.421936+00:00
-- url     : https://prove2.me/submissions/22c1c97c-aae4-46f0-8566-9d72a930e7b9

module
public import Definitions.Def_VerifiedHAMT_InsertSized
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Theorems.Thm_VerifiedHAMT_insertSizedRaw_eq


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution : @containsThenInsert = @containsThenInsertImpl := by
  funext α β _ _ map key value
  simp only [containsThenInsert, containsThenInsertImpl, insertSizedImpl,
    insertSizedRaw_eq, contains, insert]
  cases containsNode map.root (hash key).toUSize key <;> rfl
end VerifiedHAMT
