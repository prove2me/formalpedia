-- Prove2me | solution 1 for Rollback.rollback_eq_future
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:04:20.479957+00:00
-- url     : https://prove2.me/submissions/9a0f90e3-8b8b-4f47-9963-83ea6f34e4f3

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Prime_Rollback
import Theorems.Thm_Rollback_rollback_subset_future

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Rollback
open Configuration ConfFamily
local infix:50 " ⊢ " => enables es
namespace Rollback
theorem _root_.solution {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) : m.1 = c.1 \ es.future e := by
  apply Set.Subset.antisymm
  · exact rollback_subset_future (es := es) h
  · -- The canonical rollback is also a candidate, so m must contain it by maximality
    have hsub : c.1 \ es.future e ⊆ c.1 := fun x hx => hx.1
    have hnot : e ∉ c.1 \ es.future e := fun he => he.2 le_rfl
    exact h.2.2 (rollbackFuture (es := es) c e) hsub hnot (rollback_subset_future (es := es) h)
end Rollback
