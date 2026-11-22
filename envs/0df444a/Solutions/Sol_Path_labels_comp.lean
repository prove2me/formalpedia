-- Prove2me | solution 1 for Path.labels_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:25.922019+00:00
-- url     : https://prove2.me/submissions/b6b86d6c-5480-440d-be72-00aec860c5ad

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
theorem _root_.solution {c₁ c₂ c₃ : Conf F} (p₁₂ : Path F c₁ c₂) (p₂₃ : Path F c₂ c₃) :
    labels F (path_comp F p₁₂ p₂₃) = labels F p₁₂ ++ labels F p₂₃ := by
  simp [labels, trace_comp, List.map_append]
end Path
