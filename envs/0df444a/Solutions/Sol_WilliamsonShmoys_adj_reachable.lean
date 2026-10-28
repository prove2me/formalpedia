-- Prove2me | solution 1 for WilliamsonShmoys.adj_reachable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:49:00.768534+00:00
-- url     : https://prove2.me/submissions/31252206-fab1-4012-924d-aa967c4f31cb

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u v : V}
    (h : G.Adj u v) : G.Reachable u v := h.reachable
