-- Prove2me | solution 1 for PES.minimalConflict_conflict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:34.117329+00:00
-- url     : https://prove2.me/submissions/f608859f-1b42-415b-b5bd-d2a98556d1c7

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
theorem _root_.solution {e₁ e₂ : es.Event} (h : es.minimalConflict e₁ e₂) :
    es.conflict e₁ e₂ :=
  h.1
end PES
