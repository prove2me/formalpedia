-- Prove2me | solution 1 for ThreeSum.Coloring.exists_separating_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:32.906181+00:00
-- url     : https://prove2.me/submissions/db5e4824-a5ff-4499-aa59-ef37f6b72431

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_WeightedCache3SUM_Alias_fa0a04ae1b411ac3

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution {d : ℕ} {s t u : Fin d → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ p : Parameter d, applyColor p s = 0 ∧ applyColor p t = 1 ∧
      applyColor p u = 2 := by
  obtain ⟨i, j, hst', hsu', htu'⟩ := two_coordinates_separate hst hsu htu
  let f : (Bool × Bool) → Fin 3 := fun x =>
    if x = (s i, s j) then 0 else if x = (t i, t j) then 1 else 2
  refine ⟨((i, j), f), ?_, ?_, ?_⟩
  · simp [applyColor, f]
  · simp [applyColor, f, Ne.symm hst']
  · simp [applyColor, f, Ne.symm hsu', Ne.symm htu']
end ThreeSum.Coloring
