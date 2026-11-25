-- Prove2me | solution 1 for ShannonColouring.triangle_loopless
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:43:52.939908+00:00
-- url     : https://prove2.me/submissions/287738c7-6570-4fdd-a13a-98b5078dbc73

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (i : Fin 3) : (triangle i).1 ≠ (triangle i).2 := by
  fin_cases i <;> decide
end ShannonColouring
