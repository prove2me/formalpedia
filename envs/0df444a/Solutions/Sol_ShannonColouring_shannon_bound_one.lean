-- Prove2me | solution 1 for ShannonColouring.shannon_bound_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:52:29.454684+00:00
-- url     : https://prove2.me/submissions/14902bb3-6f53-464f-9361-b8e83bf5d844

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : 3 * 1 / 2 = 1 := rfl
end ShannonColouring
