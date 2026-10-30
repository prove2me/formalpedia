-- Prove2me | solution 1 for WilliamsonShmoys.planarSimpleGraphEdgeCount_upperBound__p2m_a7addf37_64f9_4244_8efd_795054181733_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:52.536697+00:00
-- url     : https://prove2.me/submissions/7295996a-dd90-408a-a8f3-7bad11e15626
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulatedExtension_edgeCount__p2m_07bf48fb_9eeb_4a56_867a_2639c9be995e_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨T, hle, hT, hcount⟩ := WilliamsonShmoys.planarDrawingOn_triangulatedExtension_edgeCount__p2m_07bf48fb_9eeb_4a56_867a_2639c9be995e_a1 M hM hV
  omega