-- Prove2me | solution 1 for P2M_VerifiedHAMT_Map_find__insert_of_ne_3980a5173b54
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:06:10.881843+00:00
-- url     : https://prove2.me/submissions/26a858cd-c75c-4b94-af14-907964d8e64f

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_of_ne_f04aac250363


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α]
    (map : Map α β) (key q : α) (value : β) (hne : q ≠ key) :
    (map.insert key value).find? q = map.find? q :=
  VerifiedHAMT.find?_insert_of_ne map.toRaw map.valid map.unique key q value hne
end VerifiedHAMT.Map
