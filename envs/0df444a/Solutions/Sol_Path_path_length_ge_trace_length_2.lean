-- Prove2me | solution 2 for Path.path_length_ge_trace_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:35.732244+00:00
-- url     : https://prove2.me/submissions/5b149fef-62ea-4809-9bea-da6b05b339f4

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
namespace Path
theorem _root_.solution {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    length F p = (trace F p).length :=
  rfl
end Path
