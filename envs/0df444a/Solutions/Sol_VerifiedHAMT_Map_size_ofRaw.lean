-- Prove2me | solution 1 for VerifiedHAMT.Map.size_ofRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:03:13.853363+00:00
-- url     : https://prove2.me/submissions/14fa63e0-f2a0-4119-b871-42909a1de256

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
theorem _root_.solution (raw : Lean.PersistentHashMap α β)
    (valid : Valid raw) (unique : Unique raw.root) :
    (ofRaw raw valid unique).size = keyCount raw.root := rfl
end VerifiedHAMT.Map
