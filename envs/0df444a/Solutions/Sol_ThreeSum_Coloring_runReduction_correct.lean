-- Prove2me | solution 1 for ThreeSum.Coloring.runReduction_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:13.073843+00:00
-- url     : https://prove2.me/submissions/30c4bc43-6ec7-4f99-916c-145ceb5ea758

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
import Theorems.Thm_ThreeSum_Coloring_reduction_correct

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution {n : ℕ} (x : Fin n → ℤ)
    (solve : Finset ℤ → Finset ℤ → Finset ℤ → Bool)
    (hsolve : ∀ a b c, solve a b c = true ↔ ThreeSetWitness a b c) :
    runReduction x solve = true ↔ DistinctZeroSum x := by
  rw [reduction_correct]
  simp only [runReduction, decide_eq_true_eq, hsolve]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨colorIndex p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, hp⟩
  · rintro ⟨c, hc, hp⟩
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨p, hp⟩
end ThreeSum.Coloring
