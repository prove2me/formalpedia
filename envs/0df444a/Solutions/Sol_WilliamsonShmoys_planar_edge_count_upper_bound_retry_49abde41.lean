-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_retry_49abde41
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:08:40.331987+00:00
-- url     : https://prove2.me/submissions/ffddef7d-683a-4fec-bade-930c242afc40

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_triangulation_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    (H.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hsub, hcard⟩ :=
    WilliamsonShmoys.planar_simple_graph_triangulation_augmentation H hH hCard
  have hmono : H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_mono hsub
  omega