-- Prove2me | solution 1 for Rollback.rollback_subset_future
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:02:50.735804+00:00
-- url     : https://prove2.me/submissions/d486deee-40f4-42df-af43-d5757cc30bd0

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
theorem _root_.solution {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) : m.1 ⊆ c.1 \ es.future e := by
  intro x hx
  refine ⟨h.1 hx, ?_⟩
  intro hxFuture
  have hle : e ≤ x := hxFuture
  have hemem : e ∈ m.1 := (m.2).2 hx hle
  exact h.2.1 hemem
end Rollback
