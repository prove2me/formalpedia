-- Prove2me | solution 1 for VerifiedHAMT.Map.nodup_keys
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:59:49.467218+00:00
-- url     : https://prove2.me/submissions/960b02b4-696a-45ee-a9d1-85db725a43a3

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
public import Theorems.Thm_VerifiedHAMT_nodup_keyList


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
namespace VerifiedHAMT.Map
theorem _root_.solution (map : Map α β) : map.keys.Nodup :=
  nodup_keyList map.valid map.unique
end VerifiedHAMT.Map
