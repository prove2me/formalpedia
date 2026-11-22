-- Prove2me | solution 1 for Rollback.rollback_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:39.459859+00:00
-- url     : https://prove2.me/submissions/6bacd47f-11ad-4eed-9ee3-9ffceb6506b6

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Rollback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Prime_Rollback
import Theorems.Thm_Rollback_rollback_future
import Theorems.Thm_Rollback_rollback_unique

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Rollback
open Configuration ConfFamily
local infix:50 " ⊢ " => enables es
namespace Rollback
theorem _root_.solution {c : Conf es} {e : es.Event} {m : Conf es}
    (h : isRollback es.toFamily c e m) :
    ∀ m' : Conf es, m' ∈ RollbackCandidates es.toFamily c e → m'.1 ⊆ m.1 := by
  -- By uniqueness, m equals the canonical rollback
  have : m = rollbackFuture (es := es) c e :=
    rollback_unique (es := es) h (rollback_future (es := es))
  cases this
  -- Now show any candidate is a subset of the canonical rollback
  intro m' ⟨hm'sub, hm'not⟩ x hx
  exact ⟨hm'sub hx, fun hxFuture => hm'not (m'.2.2 hx hxFuture)⟩
end Rollback
