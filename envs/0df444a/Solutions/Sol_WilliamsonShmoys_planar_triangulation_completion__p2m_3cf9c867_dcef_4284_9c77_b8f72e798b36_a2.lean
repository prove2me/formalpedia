-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_3cf9c867_dcef_4284_9c77_b8f72e798b36_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:34:22.559292+00:00
-- url     : https://prove2.me/submissions/ecb7c4fe-50fa-44ff-b149-1cc5cc141eef

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_completion__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_has_exact_edge_count__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V =>
      And (LE.le K L) (And (WilliamsonShmoys.HasPlanarDrawingOn L)
        (3 * Fintype.card V - 6 = L.edgeSet.ncard)) := by
  let hcompletion :=
    WilliamsonShmoys.planar_edge_maximal_completion__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
      K hK
  let L := Classical.choose hcompletion
  have hprops := Classical.choose_spec hcompletion
  refine Exists.intro L (And.intro hprops.1 (And.intro hprops.2.1 ?_))
  exact WilliamsonShmoys.planar_edge_maximal_has_exact_edge_count__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
    L hcard hprops.2.1 hprops.2.2