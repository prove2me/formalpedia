-- Prove2me | solution 1 for VerifiedHAMT.Map.toRaw_ofRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:19.896839+00:00
-- url     : https://prove2.me/submissions/2e6e429e-d402-44a3-b34f-d89f9cb6d815

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
    (ofRaw raw valid unique).toRaw = raw := rfl
end VerifiedHAMT.Map
