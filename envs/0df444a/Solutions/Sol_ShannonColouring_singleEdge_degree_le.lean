-- Prove2me | solution 1 for ShannonColouring.singleEdge_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:35:21.337788+00:00
-- url     : https://prove2.me/submissions/c5fccedf-4e37-4ef2-ab3a-fa934307128a

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (v : Fin 2) : degree singleEdge v ≤ 1 := by
  fin_cases v <;> decide
end ShannonColouring
