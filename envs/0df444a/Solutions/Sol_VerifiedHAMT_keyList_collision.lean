-- Prove2me | solution 1 for VerifiedHAMT.keyList_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:01.51093+00:00
-- url     : https://prove2.me/submissions/68665927-e6c3-48e6-8204-5ad2ffb60861

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} : keyList (.collision keys vals hsz) = keys.toList := by
  simp [keyList]
end VerifiedHAMT
