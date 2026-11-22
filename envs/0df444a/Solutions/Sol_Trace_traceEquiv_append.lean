-- Prove2me | solution 1 for Trace.traceEquiv_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:59.005163+00:00
-- url     : https://prove2.me/submissions/f4805806-b493-4d9d-948b-f4ebffbdd156

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Theorems.Thm_Trace_traceEquiv_append_left
import Theorems.Thm_Trace_traceEquiv_append_right

set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R
open Trace
namespace Trace
theorem _root_.solution {t₁ t₂ t₃ t₄ : List α}
    (h₁ : t₁ ≈ₜ t₂) (h₂ : t₃ ≈ₜ t₄) : (t₁ ++ t₃) ≈ₜ (t₂ ++ t₄) :=
  _root_.trans (traceEquiv_append_right R h₁ t₃) (traceEquiv_append_left R h₂ t₂)
end Trace
