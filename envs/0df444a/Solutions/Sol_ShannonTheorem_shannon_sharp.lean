-- Prove2me | solution 1 for ShannonTheorem.shannon_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:02:30.780811+00:00
-- url     : https://prove2.me/submissions/d88e2c9d-be02-42fc-93c5-7081213f44fc

module
public import Mathlib
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonEdgeColouring_Solution
public import Theorems.Thm_ShannonColouring_shannon_sharp


set_option autoImplicit true
@[expose] public section
public section
open ShannonTheorem
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
namespace ShannonTheorem
theorem _root_.solution (Δ : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (ends : ι → Fin 3 × Fin 3),
    (∀ i, (ends i).1 ≠ (ends i).2) ∧ (∀ v, degree ends v ≤ Δ) ∧
    ∀ k < 3 * Δ / 2, ¬ ∃ c : ι → Fin k, IsProperEdgeColouring ends c :=
  ShannonColouring.shannon_sharp Δ
end ShannonTheorem
