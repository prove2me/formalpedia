-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.wellFormed_mkCollisionNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:51.306818+00:00
-- url     : https://prove2.me/submissions/be4ab598-ff4c-4353-8af6-c714d41e2c7d

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution (hashAt : α → USize) (k₁ k₂ : α) :
    WellFormed hashAt (mkCollisionNode k₁ k₂) := .collision _ _
end VerifiedHAMT.SetWithoutValArray.Raw
