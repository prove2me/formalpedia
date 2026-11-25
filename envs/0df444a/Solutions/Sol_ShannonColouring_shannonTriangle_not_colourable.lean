-- Prove2me | solution 1 for ShannonColouring.shannonTriangle_not_colourable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:35:56.364124+00:00
-- url     : https://prove2.me/submissions/9f1f7235-393f-416e-b607-1a77f6563f8c

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp
public import Theorems.Thm_ShannonColouring_shannonTriangle_adjacent
public import Theorems.Thm_ShannonColouring_card_shannonTriangleEdge

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (Δ k : ℕ) (hk : k < 3 * Δ / 2) :
    ¬ ∃ c : ShannonTriangleEdge Δ → Fin k, IsProperEdgeColouring (shannonTriangle Δ) c := by
  rintro ⟨c, hc⟩
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    exact hc i j hne (shannonTriangle_adjacent Δ i j) hij
  have := Fintype.card_le_of_injective c hinj
  rw [card_shannonTriangleEdge, Fintype.card_fin] at this
  omega
end ShannonColouring
