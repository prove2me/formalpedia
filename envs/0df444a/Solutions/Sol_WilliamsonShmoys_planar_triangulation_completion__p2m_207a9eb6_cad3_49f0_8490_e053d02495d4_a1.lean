-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_207a9eb6_cad3_49f0_8490_e053d02495d4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:57.336637+00:00
-- url     : https://prove2.me/submissions/21a016dc-7143-476a-ad02-a420aa171706
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_drawable_supergraph__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    Exists fun M : SimpleGraph V =>
      Set.Subset H.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hHM, hMDraw, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_drawable_supergraph__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
      H hDraw
  refine ⟨M, hHM, hMDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
    M hMDraw hV hMax