-- Prove2me | solution 1 for Path.trace_length_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:32.182497+00:00
-- url     : https://prove2.me/submissions/9a5009e9-0717-47cd-8960-ae292242a618

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
    (trace F p).length = length F p :=
  rfl
end Path
