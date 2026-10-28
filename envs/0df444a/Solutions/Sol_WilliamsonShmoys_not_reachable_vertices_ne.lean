-- Prove2me | solution 1 for WilliamsonShmoys.not_reachable_vertices_ne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:34:06.465246+00:00
-- url     : https://prove2.me/submissions/2c0c63ac-d5d9-443a-bb99-f5672c13f3a1

import Mathlib

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    {u v : V}
    (hUnreachable : ¬ G.Reachable u v) :
    u ≠ v := by
  rintro rfl; exact hUnreachable (SimpleGraph.Reachable.refl u)
end WilliamsonShmoys

