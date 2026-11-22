-- Prove2me | solution 1 for Rollback.rollbackFuture_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:00:59.742911+00:00
-- url     : https://prove2.me/submissions/6613ef73-bbc0-4a19-b3bd-1d2e4a58439f

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
theorem _root_.solution {c : Conf es} {e : es.Event} {x : es.Event} :
    x ∈ (rollbackFuture (es := es) c e).1 ↔ x ∈ c.1 ∧ x ∉ es.future e :=
  Iff.rfl
end Rollback
