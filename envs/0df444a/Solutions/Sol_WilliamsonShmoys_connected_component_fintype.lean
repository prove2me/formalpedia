-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_fintype
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:36:15.738303+00:00
-- url     : https://prove2.me/submissions/ce079ea9-7801-4c62-a9d8-59b03b5304e6

import Mathlib
theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    Nonempty (Fintype G.ConnectedComponent) := by
  classical
  exact ⟨inferInstance⟩
