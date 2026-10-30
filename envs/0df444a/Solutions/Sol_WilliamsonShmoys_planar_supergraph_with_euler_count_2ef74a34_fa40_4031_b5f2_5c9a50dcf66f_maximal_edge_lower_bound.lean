-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:51:06.96405+00:00
-- url     : https://prove2.me/submissions/2f43cf9e-9b92-4b7e-866b-c91f9db351f5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hU, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_completion
      (V := V) T hV hT
  have hUT : U = T := hmax U hTU hU
  have hbound : 3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := le_of_eq hcount
  simpa [hUT] using hbound