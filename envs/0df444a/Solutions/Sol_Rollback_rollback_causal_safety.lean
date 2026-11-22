-- Prove2me | solution 1 for Rollback.rollback_causal_safety
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:28.460504+00:00
-- url     : https://prove2.me/submissions/49cb0c07-4914-4988-8e74-e0d165890f16

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
    x ∈ (rollbackFuture (es := es) c e).1 → x ∉ es.future e :=
  fun hx => hx.2
end Rollback
