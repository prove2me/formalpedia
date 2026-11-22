-- Prove2me | solution 1 for Rollback.rollback_future
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:01:11.926911+00:00
-- url     : https://prove2.me/submissions/f3527146-2a30-4504-b570-e8669ced3801

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
theorem _root_.solution {c : Conf es} {e : es.Event} :
    isRollback es.toFamily c e (rollbackFuture (es := es) c e) := by
  constructor
  · exact fun _ hx => hx.1  -- Subset of c
  constructor
  · exact fun he => he.2 le_rfl  -- e not in rollback
  · -- Maximality
    intro m' hm'sub hm'not _ _ hx
    have hxc : _ ∈ c.1 := hm'sub hx
    have hxnot : _ ∉ es.future e := fun h => hm'not (m'.2.2 hx h)
    exact ⟨hxc, hxnot⟩
end Rollback
