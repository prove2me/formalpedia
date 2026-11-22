-- Prove2me | solution 1 for Rollback.rollbackFuture_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:00:54.044189+00:00
-- url     : https://prove2.me/submissions/11d076d2-659f-4c81-9eb9-d5c741eb0a3e

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Prime_Rollback

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Rollback
open Configuration ConfFamily
local infix:50 " ⊢ " => enables es
namespace Rollback
theorem _root_.solution (c : Conf es) (e : es.Event) :
    (rollbackFuture (es := es) c e).1 = c.1 \ es.future e :=
  rfl
end Rollback
