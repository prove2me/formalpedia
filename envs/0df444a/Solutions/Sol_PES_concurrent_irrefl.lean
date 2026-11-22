-- Prove2me | solution 1 for PES.concurrent_irrefl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:45:46.108126+00:00
-- url     : https://prove2.me/submissions/efcf82e5-ff04-4f20-a43f-3325e9dd0e4e

import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Basic

set_option autoImplicit true
open PES
variable {L : Type*} (es : PES L)
local infixl:50 " # " => es.conflict
local infixl:50 " ⋈ " => es.concurrent
namespace PES
theorem _root_.solution : ∀ e, ¬ es.concurrent e e :=
  fun _ ⟨_, hNotLe, _⟩ => hNotLe le_rfl
end PES
