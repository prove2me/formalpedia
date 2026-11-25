-- Prove2me | solution 1 for ShannonColouring.card_shannonTriangleEdge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:58:57.913871+00:00
-- url     : https://prove2.me/submissions/d1ad47f9-8e0f-441d-bcd3-582478dcb89f

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : Fintype.card (ShannonTriangleEdge 1) = 1 := rfl
end ShannonColouring
