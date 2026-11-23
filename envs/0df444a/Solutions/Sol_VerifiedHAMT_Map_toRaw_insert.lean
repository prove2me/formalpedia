-- Prove2me | solution 1 for VerifiedHAMT.Map.toRaw_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:26.568466+00:00
-- url     : https://prove2.me/submissions/e7e1375c-33e4-43bc-abe5-007592fa97c3

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).toRaw = VerifiedHAMT.insert map.toRaw key value := rfl
end VerifiedHAMT.Map
