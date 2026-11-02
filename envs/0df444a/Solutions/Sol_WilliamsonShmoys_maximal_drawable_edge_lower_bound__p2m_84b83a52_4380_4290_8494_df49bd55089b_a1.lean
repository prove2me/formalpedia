-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:02.518209+00:00
-- url     : https://prove2.me/submissions/5b45e753-fb50-405e-b8ea-a6bc049d140b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_4adfb18f_d05e_40a4_90b7_ec7e79d3a996_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      ∀ u v, P.Adj u v → N.Adj u v) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨P, hsub, hP, htri⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_4adfb18f_d05e_40a4_90b7_ec7e79d3a996_a2
      N hcard hN
  have hback : ∀ u v, P.Adj u v → N.Adj u v := hmax P hsub hP
  have hEq : N = P := by
    ext u v
    exact ⟨hsub u v, hback u v⟩
  rw [hEq]
  exact le_of_eq htri