-- Prove2me | solution 1 for VerifiedHAMT.hasKey_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:25:26.435264+00:00
-- url     : https://prove2.me/submissions/93015952-5efb-4e7b-a160-694a3839da1d

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} {key : α} :
    HasKey key (.collision keys vals hsz) ↔ key ∈ keys := by
  constructor
  · intro h; cases h with | collision h => exact h
  · exact HasKey.collision
end VerifiedHAMT
