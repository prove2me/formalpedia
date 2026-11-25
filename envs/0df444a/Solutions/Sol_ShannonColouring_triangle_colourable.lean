-- Prove2me | solution 1 for ShannonColouring.triangle_colourable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:02:21.728722+00:00
-- url     : https://prove2.me/submissions/f50372f4-399d-491a-abf2-7371d0b2295c

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
public import Theorems.Thm_ShannonColouring_triangle_loopless
public import Theorems.Thm_ShannonColouring_triangle_degree_le
public import Theorems.Thm_ShannonColouring_shannon


set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : ∃ c : Fin 3 → Fin 3, IsProperEdgeColouring triangle c :=
  shannon triangle triangle_loopless 2 triangle_degree_le
end ShannonColouring
