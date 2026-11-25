-- Prove2me | solution 1 for ShannonColouring.shannon_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:46:49.540174+00:00
-- url     : https://prove2.me/submissions/1c3c6e33-264c-4f17-83d6-1c00eb530099

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp
public import Theorems.Thm_ShannonColouring_shannonTriangle_loopless
public import Theorems.Thm_ShannonColouring_degree_shannonTriangle_le
public import Theorems.Thm_ShannonColouring_shannonTriangle_not_colourable

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (Δ : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (ends : ι → Fin 3 × Fin 3),
    (∀ i, (ends i).1 ≠ (ends i).2) ∧ (∀ v, degree ends v ≤ Δ) ∧
    ∀ k < 3 * Δ / 2, ¬ ∃ c : ι → Fin k, IsProperEdgeColouring ends c :=
  ⟨ShannonTriangleEdge Δ, inferInstance, shannonTriangle Δ, shannonTriangle_loopless Δ,
    degree_shannonTriangle_le Δ, shannonTriangle_not_colourable Δ⟩
end ShannonColouring
