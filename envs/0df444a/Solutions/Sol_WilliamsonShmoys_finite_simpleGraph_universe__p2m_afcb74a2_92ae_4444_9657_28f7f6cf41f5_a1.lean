-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_universe__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:09:29.606365+00:00
-- url     : https://prove2.me/submissions/26041f7a-2b61-42dd-8469-caade0778fca

import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem _root_.solution
    {V : Type} [Fintype V] :
    (Set.univ : Set (SimpleGraph V)).Finite := by
  have hF : Finite (SimpleGraph V) :=
    Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
  exact Set.toFinite _
