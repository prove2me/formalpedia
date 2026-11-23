-- Prove2me | solution 1 for VerifiedHAMT.wellFormed_mkCollisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:23.340808+00:00
-- url     : https://prove2.me/submissions/4c1ad93c-7cdb-4080-bdc7-634c3f72aade

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
theorem _root_.solution (hashAt : α → USize) (k₁ k₂ : α) (v₁ v₂ : β) :
    WellFormed hashAt (mkCollisionNode k₁ v₁ k₂ v₂) := .collision _ _ _ _
end VerifiedHAMT
