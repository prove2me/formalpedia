-- Prove2me | solution 1 for WilliamsonShmoys.connectedComponent_support_induce_connected_4db24ad1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:13:49.080648+00:00
-- url     : https://prove2.me/submissions/209bd527-cc2e-4270-ba27-a5b0f9001607

import Mathlib

set_option autoImplicit false

open SimpleGraph
theorem solution
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    [Fintype (↥C.supp)] :
    (L.induce C.supp).Connected :=
  (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp C).1
