-- Prove2me | solution 1 for Path.minPathLength_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:06.860941+00:00
-- url     : https://prove2.me/submissions/155cd39e-c184-4b38-b2d6-3f7d0c255612

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
theorem _root_.solution {c₁ c₂ : Conf F} (h : Nonempty (Path F c₁ c₂)) :
    ∃ p : Path F c₁ c₂, length F p = minPathLength (F := F) h := by
  classical
  simpa [minPathLength] using (Nat.find_spec (pathLengthExists (F := F) h))
end Path
