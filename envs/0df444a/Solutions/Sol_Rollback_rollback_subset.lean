-- Prove2me | solution 1 for Rollback.rollback_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:00:09.44543+00:00
-- url     : https://prove2.me/submissions/d869b303-fae4-4141-b128-c48bab55b86d

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Reachability
import Definitions.Def_EventStructures_Family_Rollback

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open Rollback
namespace Rollback
theorem _root_.solution {c : Conf F} {e : F.Event} {m : Conf F}
    (h : isRollback F c e m) : m.1 ⊆ c.1 :=
  h.1
end Rollback
