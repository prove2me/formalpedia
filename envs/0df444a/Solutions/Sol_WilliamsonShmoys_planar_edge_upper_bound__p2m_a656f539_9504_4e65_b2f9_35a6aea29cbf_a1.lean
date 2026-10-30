-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:33:44.756015+00:00
-- url     : https://prove2.me/submissions/90ee8184-56aa-4f97-af5c-787b9c458fd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_73f2721b_9638_40de_84f2_73b0dfd4838a_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨T, hsub, _hplanar, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_73f2721b_9638_40de_84f2_73b0dfd4838a_a2 L hL hV
  have hle : L.edgeSet.ncard <= T.edgeSet.ncard := Set.ncard_mono hsub
  omega
