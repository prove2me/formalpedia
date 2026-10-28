-- Prove2me | solution 1 for WilliamsonShmoys.drawable_edgeSet_ncard_mono_3daf7e3a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:33:17.30446+00:00
-- url     : https://prove2.me/submissions/59117e7b-a2a3-4855-a12d-b3cad5b499a6

import Mathlib

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P Q : SimpleGraph V) (hPQ : P ≤ Q) :
    P.edgeSet.ncard ≤ Q.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hPQ) (Set.toFinite _)
end WilliamsonShmoys

