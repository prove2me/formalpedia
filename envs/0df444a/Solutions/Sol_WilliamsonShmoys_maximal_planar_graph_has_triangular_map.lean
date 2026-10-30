-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_triangular_map
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:17:56.147095+00:00
-- url     : https://prove2.me/submissions/16f3d07c-5fe3-40cf-bf7a-0a7c4488a3f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_7369a359
import Theorems.Thm_WilliamsonShmoys_planar_maximum_edge_count_to_triangular_map__p2m_c83adf6f_1433_4aa5_8a45_3bb46fb3b994_a45

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V), K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    ∃ (m : Nat), Nonempty (WilliamsonShmoys.TriangularMap K (Fin m)) := by
  obtain ⟨H, hKH, hHd, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359
      K hK hV
  have hHK : H = K := hmax H hKH hHd
  subst H
  exact WilliamsonShmoys.planar_maximum_edge_count_to_triangular_map__p2m_c83adf6f_1433_4aa5_8a45_3bb46fb3b994_a45
    K hHd hV hcount