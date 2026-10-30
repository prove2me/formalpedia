-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_ba8b1886_1f4e_4f59_8448_b70c4d0c6621
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:47:10.527663+00:00
-- url     : https://prove2.me/submissions/43d3ba4b-0e14-4a0a-820e-782359a0036b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_maximal_extension_19f31498_c1c5_41a0_a186_562a063d6dde
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_maximal_extension_19f31498_c1c5_41a0_a186_562a063d6dde K hK
  refine ⟨H, hKH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde H hV hH hMax