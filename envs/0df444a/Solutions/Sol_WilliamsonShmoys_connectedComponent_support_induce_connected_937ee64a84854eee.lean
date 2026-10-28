-- Prove2me | solution 1 for WilliamsonShmoys.connectedComponent_support_induce_connected_937ee64a84854eee
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:33:45.685989+00:00
-- url     : https://prove2.me/submissions/165d80e3-72fc-4a05-9e28-f99775a83f78

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
