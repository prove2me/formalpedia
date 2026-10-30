-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_same_vertices__p2m_5db777ea_26b2_4b9c_844f_64ae8eedcb74_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:26:01.648992+00:00
-- url     : https://prove2.me/submissions/41a6c6d5-ce55-420f-915f-057edc8f3d7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_maximal_planar_supergraph__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_maximal_edge_count__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.planar_triangulation_maximal_planar_supergraph__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
      T hT
  exact ⟨U, hTU, hU,
    WilliamsonShmoys.planar_triangulation_maximal_edge_count__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
      U hU hV hmax⟩