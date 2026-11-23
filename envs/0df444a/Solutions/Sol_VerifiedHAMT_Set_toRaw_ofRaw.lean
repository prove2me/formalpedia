-- Prove2me | solution 1 for VerifiedHAMT.Set.toRaw_ofRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:56:10.609192+00:00
-- url     : https://prove2.me/submissions/48b0a76b-55ee-4bef-93aa-b60f18a8f5e4

module
public import Definitions.Def_VerifiedHAMT_Map
public import Lean.Data.PersistentHashSet
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashSet
public import Definitions.Def_VerifiedHAMT_Set

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Set
variable {α : Type u} [BEq α] [Hashable α]
namespace VerifiedHAMT.Set
theorem _root_.solution (raw : Lean.PersistentHashSet α)
    (valid : Valid raw.set) (unique : Unique raw.set.root) :
    (ofRaw raw valid unique).toRaw = raw := rfl
end VerifiedHAMT.Set
