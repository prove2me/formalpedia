-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_f922730b_ca22_4588_ba9a_35deaa5a3fb1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:45:36.570204+00:00
-- url     : https://prove2.me/submissions/6800c616-57ca-4856-9b44-6c60e6e0b9b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_triangulation__p2m_75470aa8_21fb_4723_a0a9_53d10a7cd9b1_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel _
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨K, hHK, hKplanar, hKcard⟩ :=
    WilliamsonShmoys.planar_extension_to_triangulation__p2m_75470aa8_21fb_4723_a0a9_53d10a7cd9b1_a1 H hH hn
  have hKH : K = H := hmax K hHK hKplanar
  rw [hKH] at hKcard
  exact hKcard
