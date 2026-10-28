-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:30:41.024118+00:00
-- url     : https://prove2.me/submissions/ebc700cc-4a64-43e9-b70a-457026554b0d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_property_18bde782_847e_438f_96b7_cc5ed2ba2f1b

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    Exists fun T : SimpleGraph V =>
      And (LE.le L T) (And (WilliamsonShmoys.HasPlanarDrawingOn T)
        (forall U : SimpleGraph V, LE.le T U ->
          WilliamsonShmoys.HasPlanarDrawingOn U -> LE.le U T)) := by
  classical
  exact WilliamsonShmoys.exists_maximal_supergraph_of_finite_property_18bde782_847e_438f_96b7_cc5ed2ba2f1b
    L WilliamsonShmoys.HasPlanarDrawingOn hL