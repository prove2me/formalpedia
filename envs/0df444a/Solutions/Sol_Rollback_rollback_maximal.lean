-- Prove2me | solution 1 for Rollback.rollback_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:09.458435+00:00
-- url     : https://prove2.me/submissions/f5ca6317-8d5a-4c05-a68f-b1f95e926809

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback
namespace Rollback
theorem _root_.solution {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) :
    ∀ m' : Conf F, m'.1 ⊆ c.1 → e ∉ m'.1 → m.1 ⊆ m'.1 → m'.1 ⊆ m.1 :=
  h.2.2
end Rollback
