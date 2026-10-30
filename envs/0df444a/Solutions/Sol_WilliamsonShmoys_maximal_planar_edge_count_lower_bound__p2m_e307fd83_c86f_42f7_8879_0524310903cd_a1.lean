-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e307fd83_c86f_42f7_8879_0524310903cd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:59.787371+00:00
-- url     : https://prove2.me/submissions/262afd21-bfae-47df-838d-58a21e569bd4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_of_le__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ K : SimpleGraph V,
      G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ G)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hKDrawing, hExact⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
      G hG hV
  have hKG : K ≤ G := hMax K hGK hKDrawing
  have hCount :=
    WilliamsonShmoys.edgeSet_ncard_mono_of_le__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1 hKG
  omega