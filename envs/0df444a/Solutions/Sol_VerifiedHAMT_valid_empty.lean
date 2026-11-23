-- Prove2me | solution 1 for VerifiedHAMT.valid_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:02.326143+00:00
-- url     : https://prove2.me/submissions/f84d48a6-06cc-4e44-97f4-fa6b37c46e1e

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
public import Theorems.Thm_VerifiedHAMT_wellFormed_empty

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [Hashable α] :
    Valid (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β) :=
  wellFormed_empty _
end VerifiedHAMT
