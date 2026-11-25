-- Prove2me | solution 1 for ShannonColouring.triangle_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:44:25.42188+00:00
-- url     : https://prove2.me/submissions/3051668e-dc97-4f80-abf2-9f0c834c117f

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution (v : Fin 3) : degree triangle v ≤ 2 := by
  fin_cases v <;> decide
end ShannonColouring
