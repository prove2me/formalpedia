-- Prove2me | solution 1 for ShannonTheorem.shannon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:06:32.016286+00:00
-- url     : https://prove2.me/submissions/96d8f522-d645-4983-8409-e58891017310

module
public import Mathlib
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonEdgeColouring_Solution
public import Theorems.Thm_ShannonColouring_shannon


set_option autoImplicit true
@[expose] public section
public section
open ShannonTheorem
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
namespace ShannonTheorem
theorem _root_.solution {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] (ends : ι → V × V)
    (hloop : ∀ i, (ends i).1 ≠ (ends i).2) (Δ : ℕ) (hΔ : ∀ v, degree ends v ≤ Δ) :
    ∃ c : ι → Fin (3 * Δ / 2), IsProperEdgeColouring ends c :=
  ShannonColouring.shannon ends hloop Δ hΔ
end ShannonTheorem
