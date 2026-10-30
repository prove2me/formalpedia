-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:42.550772+00:00
-- url     : https://prove2.me/submissions/6d9dceae-3a10-409a-adb2-7f0962660c3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V)
    (hV : LE.le 3 (Fintype.card V))
    (hsub : Set.Subset K.edgeSet H.edgeSet)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall H' : SimpleGraph V,
      Set.Subset H.edgeSet H'.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn H' ->
      H'.edgeSet = H.edgeSet) :
    Exists fun f : Nat => And (Fintype.card V + f = H.edgeSet.ncard + 2)
      (3 * f = 2 * H.edgeSet.ncard) := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1 H hV hdraw hmax
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1 H hV hdraw hmax
  have hm : H.edgeSet.ncard + 6 = 3 * Fintype.card V := Nat.le_antisymm hupper hlower
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  constructor <;> omega