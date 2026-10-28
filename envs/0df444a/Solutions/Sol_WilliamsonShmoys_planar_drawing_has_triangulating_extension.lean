-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulating_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:08:34.802614+00:00
-- url     : https://prove2.me/submissions/de51da49-298e-41ff-84ce-6cb7e5537844
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_for_triangulating_extension_8070196b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_for_triangulating_extension_8070196b

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T.edgeSet ⊆ U.edgeSet ∧
      HasPlanarDrawingOn U ∧
      T.edgeSet.ncard ≤ U.edgeSet.ncard ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulating_extension_8070196b T hT
  have hcount :=
    WilliamsonShmoys.maximal_planar_supergraph_edge_count_for_triangulating_extension_8070196b
      T U hV hT hTU hU hmax
  exact ⟨U, hTU, hU, Set.ncard_le_ncard hTU, hcount⟩
