-- Prove2me | solution 2 for Path.trace_of_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:12:32.616394+00:00
-- url     : https://prove2.me/submissions/e8ee313f-b956-4479-a8f6-fbb3177b97d4

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Nat.Find
import Definitions.Def_EventStructures_Family_Path
import Theorems.Thm_Path_path_subset

set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
local infix:50 " ⊢ " => enables F
open Path
local infixr:60 " ≈ₚ " => PathEquiv F
namespace Path
theorem _root_.solution {c₁ c₂ : Conf F} (p : Path F c₁ c₂) :
    ∀ e ∈ trace F p, e ∈ c₂.1 := by
  induction p with
  | refl => simp [trace]
  | @step c₁ c₂ c₃ hEdge hPath ih =>
    intro e he
    simp only [trace, List.mem_cons] at he
    rcases he with rfl | h_in_rest
    · -- Head event is in c₂, and c₂ ⊆ c₃ by path_subset
      have h_in_c₂ : hEdge.event ∈ c₂.1 := by
        rw [hEdge.conf₂_equals]
        simp
      exact (path_subset (F := F) hPath) h_in_c₂
    · -- Tail event is in c₃ by IH
      exact ih e h_in_rest
end Path
