-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:07:29.526981+00:00
-- url     : https://prove2.me/submissions/deefe634-bf2d-44c2-aceb-f60ce069909c

import Definitions.Def_WilliamsonShmoys_TriangularMap
theorem solution
    {V : Type} [Fintype V] :
    Finite (SimpleGraph V) := by 
  classical
  infer_instance
