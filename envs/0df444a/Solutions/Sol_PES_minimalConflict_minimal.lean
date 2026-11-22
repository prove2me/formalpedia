-- Prove2me | solution 1 for PES.minimalConflict_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:35.007432+00:00
-- url     : https://prove2.me/submissions/88c82fd2-dbc1-487c-ad15-2cd5c3bde85d

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
theorem _root_.solution {e₁ e₂ e₁' e₂' : es.Event} (h : es.minimalConflict e₁ e₂)
    (he₁ : e₁' ≤ e₁) (he₂ : e₂' ≤ e₂) (hConf : es.conflict e₁' e₂') :
    e₁' = e₁ ∧ e₂' = e₂ :=
  h.2 e₁' e₂' he₁ he₂ hConf
end PES
