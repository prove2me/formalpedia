-- Prove2me | solution 1 for WilliamsonShmoys.planar_edgeSet_ncard_mono_for_maximal_planar_drawing_edge_lower_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:13:11.518761+00:00
-- url     : https://prove2.me/submissions/fe9c1f98-ab9c-44c0-bb59-90f7f2a247c0

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : LE.le G H) :
    G.edgeSet.ncard <= H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
