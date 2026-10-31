-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:37:32.206111+00:00
-- url     : https://prove2.me/submissions/f67f6ba0-f968-427c-9c50-96fc4acf2b60

import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangular_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ := WilliamsonShmoys.maximal_planar_euler_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1 H hplanar hV hmax
  have hTriangle := WilliamsonShmoys.maximal_planar_triangular_faces__p2m_45858051_39d1_461c_bf97_6d18e2a89002_a1 H hplanar hV hmax f hEuler
  omega