-- Prove2me | solution 1 for Path.trace_of_path
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T21:12:09.753818+00:00
-- url     : https://prove2.me/submissions/50d79d30-0a56-4484-adbe-f182f10939d2

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
theorem AuxTP_key {a b : Conf F} (q : Path F a b) :
    ∀ e, (e ∈ a.1 ∨ e ∈ trace F q) → e ∈ b.1 := by
  induction q with
  | refl => intro e he; simpa [trace] using he
  | step hEdge hPath ih =>
    intro e he
    have h2 := hEdge.conf₂_equals
    rcases he with he | he
    · exact ih e (Or.inl (by rw [h2]; exact Or.inl he))
    · simp only [trace, List.mem_cons] at he
      rcases he with rfl | he
      · exact ih _ (Or.inl (by rw [h2]; exact Or.inr rfl))
      · exact ih e (Or.inr he)

theorem Path.trace_of_path {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    ∀ e ∈ trace F p, e ∈ c₂.1 := by
  intro e he
  exact AuxTP_key F p e (Or.inr he)

theorem solution {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    ∀ e ∈ trace F p, e ∈ c₂.1 := Path.trace_of_path F p
