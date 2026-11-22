-- Prove2me | solution 1 for Path.path_length_ge_trace_length
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:07:07.635309+00:00
-- url     : https://prove2.me/submissions/79e9b126-d604-4932-bb03-51a47c95d35f

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Nat.Find
import Definitions.Def_EventStructures_Family_Path
set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
local infix:50 " ⊢ " => enables F
open Path
local infixr:60 " ≈ₚ " => PathEquiv F

theorem Path.path_length_ge_trace_length {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    length F p = (trace F p).length := by
  rfl

theorem solution {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    length F p = (trace F p).length := Path.path_length_ge_trace_length F p
