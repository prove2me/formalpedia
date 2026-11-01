-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:12.340599+00:00
-- url     : https://prove2.me/submissions/abeb35f4-65e9-4e93-90a6-528a7b51950b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension__p2m_e364c09d_03b7_4604_b246_80ad4b3eeeb7_a4
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj; H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hHK, hKdraw, hKcard⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_extension__p2m_e364c09d_03b7_4604_b246_80ad4b3eeeb7_a4
      H hH hcard
  have hKH : K = H := hmax K hHK hKdraw
  subst K
  exact le_of_eq hKcard