-- Prove2me | solution 1 for VerifiedHAMT.wellFormed_collisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:26:24.16854+00:00
-- url     : https://prove2.me/submissions/642eebf1-e705-47de-a660-5b4a3bead243

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
theorem _root_.solution (hashAt : α → USize) (b : CollisionNode α β) :
    WellFormed hashAt b.val := by
  obtain ⟨node, hb⟩ := b
  cases hb
  exact .collision _ _ _ _
end VerifiedHAMT
