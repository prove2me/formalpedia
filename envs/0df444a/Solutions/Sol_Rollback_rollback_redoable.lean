-- Prove2me | solution 1 for Rollback.rollback_redoable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:24.150304+00:00
-- url     : https://prove2.me/submissions/e16c8111-4108-4f2e-a18b-41831adfafe1

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
theorem _root_.solution {c : Conf es} {e : es.Event} (he : e ∈ c.1) :
    (rollbackFuture (es := es) c e).1 ⊢ e := by
  constructor
  · exact rollback_future_isConf (es := es) (c := c)
  constructor
  · -- All events in rollback are consistent with e
    intro e' he'
    exact c.2.1 he he'.1
  · -- The strict past of e is contained in rollback
    intro x hx
    have hxc : x ∈ c.1 := c.2.2 he (le_of_lt hx)
    have hxnot : x ∉ es.future e := fun h => not_le_of_gt hx h
    exact ⟨hxc, hxnot⟩
end Rollback
