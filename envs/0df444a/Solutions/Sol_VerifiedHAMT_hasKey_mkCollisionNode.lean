-- Prove2me | solution 1 for VerifiedHAMT.hasKey_mkCollisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:25:43.450294+00:00
-- url     : https://prove2.me/submissions/c4b591a2-b8d5-4e42-94b6-6f75c21950fd

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_collision
attribute [local simp] VerifiedHAMT.hasKey_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution (k₁ k₂ q : α) (v₁ v₂ : β) :
    HasKey q (mkCollisionNode k₁ v₁ k₂ v₂) ↔ q = k₁ ∨ q = k₂ := by
  simp [mkCollisionNode]
end VerifiedHAMT
