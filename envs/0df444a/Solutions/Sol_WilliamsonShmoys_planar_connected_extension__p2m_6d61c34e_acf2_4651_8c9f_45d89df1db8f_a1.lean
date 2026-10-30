-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_extension__p2m_6d61c34e_acf2_4651_8c9f_45d89df1db8f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:55:29.441083+00:00
-- url     : https://prove2.me/submissions/17a7e6f0-df04-4573-9a8d-1a084706cf8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count_54a0e51c
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_nonempty_connected__p2m_ea88c89d_48b3_414b_a3f4_04bcb156f9eb_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 1 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Connected := by
  obtain ⟨K, hLK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_54a0e51c
      L hplanar
  refine ⟨K, ?_, hK, ?_⟩
  · exact SimpleGraph.edgeSet_subset_edgeSet.mp hLK
  · exact
      WilliamsonShmoys.maximal_drawable_nonempty_connected__p2m_ea88c89d_48b3_414b_a3f4_04bcb156f9eb_a1
        K hV hK hmax