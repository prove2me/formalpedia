-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_edge_bound__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:42.322772+00:00
-- url     : https://prove2.me/submissions/d9c4ec20-73aa-4813-80ca-5840d51619a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_mono__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_completion__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hConnected : G.Connected) (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  rcases WilliamsonShmoys_connected_planar_triangulation_completion__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1
      G hDraw hConnected hCard with ⟨H, hsub, _hDrawH, hmax⟩
  have hmono := WilliamsonShmoys_planar_edgeSet_ncard_mono__p2m_203b6e6b_f468_4fb9_a6ed_110500d4f041_a1 G H hsub
  omega