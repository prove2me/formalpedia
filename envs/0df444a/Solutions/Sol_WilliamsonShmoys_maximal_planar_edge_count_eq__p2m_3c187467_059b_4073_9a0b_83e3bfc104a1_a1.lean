-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_3c187467_059b_4073_9a0b_83e3bfc104a1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:19:07.72159+00:00
-- url     : https://prove2.me/submissions/2dc9e11e-8dff-4dcd-9dbe-a37e0d917afd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_deff29d9_5a9a_4a55_a466_fc15c898aa4f_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_deff29d9_5a9a_4a55_a466_fc15c898aa4f_a1 H hV hH
  have hKH : K = H := hmax K hHK hK
  simpa [hKH] using hcount