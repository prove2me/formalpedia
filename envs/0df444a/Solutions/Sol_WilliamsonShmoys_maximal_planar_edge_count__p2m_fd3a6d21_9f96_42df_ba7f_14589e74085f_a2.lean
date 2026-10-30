-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:53:20.626279+00:00
-- url     : https://prove2.me/submissions/dc2586b9-6bb6-469d-a170-6b9e9e334e55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ->
      Set.Subset K.edgeSet H.edgeSet ->
      Set.Subset H.edgeSet K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hH, hKH, hLower⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2 K hK hV
  have hHK : Set.Subset H.edgeSet K.edgeSet := hmax H hH hKH
  have hcard : K.edgeSet.ncard = H.edgeSet.ncard :=
    Nat.le_antisymm (Set.ncard_mono hKH) (Set.ncard_mono hHK)
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2 H hH hV
  omega