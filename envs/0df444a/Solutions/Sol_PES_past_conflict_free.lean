-- Prove2me | solution 1 for PES.past_conflict_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:41.168634+00:00
-- url     : https://prove2.me/submissions/8a863157-3a11-426b-a788-7b23cc9034b3

import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Basic

set_option autoImplicit true
open PES
variable {L : Type*} (es : PES L)
local infixl:50 " # " => es.conflict
local infixl:50 " ⋈ " => es.concurrent
local infixl:50 " ## " => es.minimalConflict
namespace PES
theorem _root_.solution {e e₁ e₂ : es.Event}
    (h₁ : e₁ ≤ e) (h₂ : e₂ ≤ e) : ¬ es.conflict e₁ e₂ :=
  fun hc => es.conflict_irrefl e
    (es.conflict_hereditary (es.conflict_symm.symm _ _ (es.conflict_hereditary hc h₂)) h₁)
end PES
