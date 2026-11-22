-- Prove2me | solution 1 for Path.path_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:59:35.076517+00:00
-- url     : https://prove2.me/submissions/a93828d1-6486-4aa6-b3b0-7c8a9f5bd778

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Nat.Find
import Definitions.Def_EventStructures_Family_Path
import Theorems.Thm_ConfFamily_TraceEquivFrom_trans


set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
local infix:50 " ⊢ " => enables F
open Path
local infixr:60 " ≈ₚ " => PathEquiv F
namespace Path
theorem _root_.solution {c₁ c₂ : Conf F} (p : Path F c₁ c₂) : c₁.1 ⊆ c₂.1 := by
  induction p with
  | refl => exact Set.Subset.rfl
  | @step c₁ c₂ c₃ hEdge hPath ih =>
    have h₁₂ : c₁.1 ⊆ c₂.1 := by
      intro x hx
      have hx' : x ∈ c₁.1 ∪ {hEdge.event} := Or.inl hx
      simpa [hEdge.conf₂_equals] using hx'
    exact Set.Subset.trans h₁₂ ih
end Path
