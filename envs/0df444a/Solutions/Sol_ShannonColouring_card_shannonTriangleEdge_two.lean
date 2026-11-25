-- Prove2me | solution 1 for ShannonColouring.card_shannonTriangleEdge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:59:40.821849+00:00
-- url     : https://prove2.me/submissions/b3d526d3-c109-4e4b-bfea-8276a4ffbdf2

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : Fintype.card (ShannonTriangleEdge 2) = 3 := rfl
end ShannonColouring
