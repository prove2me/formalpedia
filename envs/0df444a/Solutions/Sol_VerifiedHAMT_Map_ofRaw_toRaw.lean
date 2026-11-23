-- Prove2me | solution 1 for VerifiedHAMT.Map.ofRaw_toRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:11.50685+00:00
-- url     : https://prove2.me/submissions/f765eb35-d842-4139-aac5-8e653050a652

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
theorem _root_.solution (map : Map α β) :
    ofRaw map.toRaw map.valid map.unique = map := by
  cases map with
  | mk data valid unique size_eq =>
    cases data with
    | mk raw size =>
      change size = keyCount raw.root at size_eq
      subst size
      rfl
end VerifiedHAMT.Map
