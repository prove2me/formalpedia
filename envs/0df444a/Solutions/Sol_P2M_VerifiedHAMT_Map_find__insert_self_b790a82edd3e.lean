-- Prove2me | solution 1 for P2M_VerifiedHAMT_Map_find__insert_self_b790a82edd3e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:05:44.215+00:00
-- url     : https://prove2.me/submissions/adf9373e-32e3-489e-ba45-614c237a66dd

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_P2M_VerifiedHAMT_find__insert_self_b1de16f2743e


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution [LawfulBEq α]
    (map : Map α β) (key : α) (value : β) :
    (map.insert key value).find? key = some value :=
  VerifiedHAMT.find?_insert_self map.toRaw map.valid map.unique key value
end VerifiedHAMT.Map
