-- Prove2me | solution 1 for VerifiedHAMT.mapsTo_insert_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:06.061812+00:00
-- url     : https://prove2.me/submissions/d6cadc07-ac0f-464d-95bc-410943007a46

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_iff
public import Theorems.Thm_VerifiedHAMT_mapsTo_insert_self
attribute [local simp] VerifiedHAMT.mapsTo_insert_self

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (hu : Unique map.root)
    (key q : α) (value w : β) (hne : q ≠ key) :
    MapsTo q w (insert map key value) ↔ MapsTo q w map := by
  simp [mapsTo_insert_iff map wf hu, hne]
end VerifiedHAMT
