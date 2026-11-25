-- Prove2me | solution 1 for ShannonColouring.singleEdge_not_colourable_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:53:38.924502+00:00
-- url     : https://prove2.me/submissions/10ee6c17-825c-4522-b2f7-c609215b5312

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution :
    ¬ ∃ c : Unit → Fin 0, IsProperEdgeColouring singleEdge c :=
  fun ⟨c, _⟩ => (c ()).elim0
end ShannonColouring
