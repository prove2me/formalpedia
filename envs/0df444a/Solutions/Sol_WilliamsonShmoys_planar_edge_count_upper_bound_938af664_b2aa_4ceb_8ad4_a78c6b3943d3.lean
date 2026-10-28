-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:33:35.330172+00:00
-- url     : https://prove2.me/submissions/d756ce10-b2c6-445d-a9a2-0b3cd3893878
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax, hcount⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_938af664_b2aa_4ceb_8ad4_a78c6b3943d3 G hV hG
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_count_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3 H hV hH hmax
  omega