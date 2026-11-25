-- Prove2me | solution 1 for ShannonColouring.shannonTriangle_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:24:52.541803+00:00
-- url     : https://prove2.me/submissions/7969dfe1-cb76-46de-8731-49abb8f9511d

module
public import Definitions.Def_ShannonColouring_Defs
public import Definitions.Def_ShannonColouring_Sharp

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (Δ : ℕ) (i j : ShannonTriangleEdge Δ) :
    ∃ v, Incident (shannonTriangle Δ) i v ∧ Incident (shannonTriangle Δ) j v := by
  rcases i with _ | _ | _ <;> rcases j with _ | _ | _ <;>
  simp only [Incident, shannonTriangle] <;> decide
end ShannonColouring
