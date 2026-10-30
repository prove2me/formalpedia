-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_42e17741_b5fb_4586_95ad_fdcb2ee9a443_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:04.921978+00:00
-- url     : https://prove2.me/submissions/508c39ba-4000-4cb2-8533-97e30963347f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V, W ≤ X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      X.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨X, hWX, hX, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
      W hW
  exact ⟨X, hWX, hX,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_3e222915_cdcc_42d9_bbed_07142c562af3_a1
      X hX hV hmax⟩