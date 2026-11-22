-- Prove2me | solution 1 for Rollback.rollback_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:00:20.228708+00:00
-- url     : https://prove2.me/submissions/30f0643f-6892-4fc2-a620-57f0a42038b8

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback
namespace Rollback
theorem _root_.solution {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : e ∉ m.1 :=
  h.2.1
end Rollback
