-- Prove2me | solution 1 for ShannonColouring.shannon_bound_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:53:28.721558+00:00
-- url     : https://prove2.me/submissions/9a3b9e8d-3684-4f12-930e-58c225e54e60

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : 3 * 3 / 2 = 4 := rfl
end ShannonColouring
