-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:39:02.032016+00:00
-- url     : https://prove2.me/submissions/9d088268-ae0e-4a81-b436-faca2d5944e1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hPlanar : HasPlanarDrawingOn K)
    (hMaximal : forall H : SimpleGraph V, K <= H -> HasPlanarDrawingOn H -> H <= K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V <= K.edgeFinset.card + 6 := by
  apply WilliamsonShmoys.planar_edge_count_lower__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1 K hV hPlanar
  intro H hKH hH
  exact le_antisymm (hMaximal H hKH hH) hKH
