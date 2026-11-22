-- Prove2me | solution 1 for Path.execList_to_path_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:10.47774+00:00
-- url     : https://prove2.me/submissions/ef0e9469-9bd1-4bc6-877c-095f713c642c

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
namespace Path
theorem _root_.solution {c₁ c₂ : Conf F} {t : List F.Event}
    (h : ExecList F c₁ t c₂) :
    trace F (execList_to_path (F := F) h) = t :=
  execList_trace (F := F) h
end Path
