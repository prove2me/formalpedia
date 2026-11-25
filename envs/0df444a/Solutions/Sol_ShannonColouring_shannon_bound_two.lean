-- Prove2me | solution 1 for ShannonColouring.shannon_bound_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:53:27.822498+00:00
-- url     : https://prove2.me/submissions/a6749478-7adb-4c56-abb9-646af9f3ddf4

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity

set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : 3 * 2 / 2 = 3 := rfl
end ShannonColouring
