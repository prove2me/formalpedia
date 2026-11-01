-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_three_n_minus_six_edges__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:04:01.109056+00:00
-- url     : https://prove2.me/submissions/f3d5530e-613d-4a03-b1a3-0351f2ac0d16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulated_supergraph__p2m_19dec27f_df1a_4e90_89f3_8f6e92e830e3_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q →
      (∀ u v, P.Adj u v → Q.Adj u v) →
      ∀ u v, Q.Adj u v → P.Adj u v) :
    P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨Q, hPQ, hQ, hcount⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulated_supergraph__p2m_19dec27f_df1a_4e90_89f3_8f6e92e830e3_a1 P hP hcard
  have hQtoP : ∀ u v, Q.Adj u v → P.Adj u v := hmax Q hQ hPQ
  have hEq : Q = P := by
    ext u v
    exact ⟨hQtoP u v, hPQ u v⟩
  simpa [hEq] using hcount