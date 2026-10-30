-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_is_inclusion_maximal__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:38:13.004056+00:00
-- url     : https://prove2.me/submissions/d2c7e96a-cbdd-4a7d-88e9-145429c546d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V)
    (hsub : Set.Subset H.edgeSet K.edgeSet) :
    K.edgeSet = H.edgeSet := by
  have hKbound :
      K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_bound__p2m_7f8156d0_59cd_483d_b914_1d18d842c166_a2
      K hK hV
  have hle : K.edgeSet.ncard + 6 <= H.edgeSet.ncard + 6 := by
    rw [hcount]
    exact hKbound
  have hcard : K.edgeSet.ncard <= H.edgeSet.ncard :=
    Nat.le_of_add_le_add_right hle
  have hEq : H.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub hcard
  exact hEq.symm