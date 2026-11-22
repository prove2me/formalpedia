-- Prove2me | solution 1 for Path.minPathLength_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:07.447267+00:00
-- url     : https://prove2.me/submissions/5f486c84-8bca-4fe9-af7b-90c723ec39bd

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
theorem _root_.solution {c₁ c₂ : Conf F} (h : Nonempty (Path F c₁ c₂)) (p : Path F c₁ c₂) :
    minPathLength (F := F) h ≤ length F p := by
  classical
  simpa [minPathLength] using (Nat.find_min' (H := pathLengthExists (F := F) h) ⟨p, rfl⟩)
end Path
