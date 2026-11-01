-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_89582c96_c588_4663_9e82_ebaf767d7a60_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:09.005927+00:00
-- url     : https://prove2.me/submissions/2ff0d232-1451-4872-81ad-aaae512c5e6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_counts__p2m_0c45b479_8ae4_466e_b4e0_c546b42868e7_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      3 * Fintype.card V - 6 = L.edgeFinset.card) := by
  classical
  obtain ⟨f, hEuler, hTriangles⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation_counts__p2m_0c45b479_8ae4_466e_b4e0_c546b42868e7_a2
      L hL hcard hmax
  omega