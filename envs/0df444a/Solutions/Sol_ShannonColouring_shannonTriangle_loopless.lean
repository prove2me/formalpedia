-- Prove2me | solution 1 for ShannonColouring.shannonTriangle_loopless
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:22:52.303852+00:00
-- url     : https://prove2.me/submissions/e6b93a8c-f379-465f-96ca-9ede71bad170

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (Δ : ℕ) (i : ShannonTriangleEdge Δ) :
    (shannonTriangle Δ i).1 ≠ (shannonTriangle Δ i).2 := by
  rcases i with _ | _ | _ <;> simp [shannonTriangle]
end ShannonColouring
