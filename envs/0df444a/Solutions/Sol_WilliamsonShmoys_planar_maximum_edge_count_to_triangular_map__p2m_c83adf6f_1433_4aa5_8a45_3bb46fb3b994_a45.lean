-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximum_edge_count_to_triangular_map__p2m_c83adf6f_1433_4aa5_8a45_3bb46fb3b994_a45
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:26:40.947578+00:00
-- url     : https://prove2.me/submissions/cdf57a12-8621-4608-a813-c86d0fc17ae3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_is_inclusion_maximal__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
import Theorems.Thm_WilliamsonShmoys_planar_inclusion_maximal_to_triangular_map__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : Nat.le 3 (Fintype.card V))
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    Exists fun m : Nat => Nonempty (WilliamsonShmoys.TriangularMap H (Fin m)) := by
  have hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet -> K.edgeSet = H.edgeSet := by
    intro K hK hsub
    exact WilliamsonShmoys.planar_edge_count_is_inclusion_maximal__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
      H K hH hK hV hcount hsub
  exact WilliamsonShmoys.planar_inclusion_maximal_to_triangular_map__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
    H hH hV hmax