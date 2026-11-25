-- Prove2me | solution 1 for ShannonColouring.card_shannonTriangleEdge_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:00:27.696304+00:00
-- url     : https://prove2.me/submissions/4b12b223-be2b-4e0d-8a42-4feeee0e8eb2

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : Fintype.card (ShannonTriangleEdge 3) = 4 := rfl
end ShannonColouring
