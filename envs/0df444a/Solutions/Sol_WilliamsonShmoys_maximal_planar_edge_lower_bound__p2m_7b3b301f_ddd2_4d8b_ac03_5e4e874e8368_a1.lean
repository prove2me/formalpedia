-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7b3b301f_ddd2_4d8b_ac03_5e4e874e8368_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:36:20.56677+00:00
-- url     : https://prove2.me/submissions/1cc03a67-7baa-4fdd-96c8-452cfd578cd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_euler_edge_count__p2m_4a9048a5_f8b9_492a_9599_928b8a8a35af_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨H, hsub, hplanar, he⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_euler_edge_count__p2m_4a9048a5_f8b9_492a_9599_928b8a8a35af_a1
      M hV hM
  have hHM : H = M := hmax H hsub hplanar
  have hcount : M.edgeSet.ncard = H.edgeSet.ncard :=
    (congrArg (fun G : SimpleGraph V => G.edgeSet.ncard) hHM).symm
  omega