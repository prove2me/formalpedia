-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_euler_face_certificate__p2m_68659add_1ba6_4067_be65_c7b40be0a2e9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:31.408626+00:00
-- url     : https://prove2.me/submissions/71851a8a-97c0-43cb-a52f-86bb2bb0ede5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_formula__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_simple_edge_bound__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 ∧
      3 * f ≤ 2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) := by
  letI : DecidableRel G.Adj := dG
  obtain ⟨f, hfEuler⟩ :=
    WilliamsonShmoys.planarDrawing_euler_formula__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
      G dG hG hConn
  have hEdges :
      G.edgeFinset.card + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planarDrawing_simple_edge_bound__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
      G dG hG hConn hcard
  exact ⟨f, hfEuler, by omega⟩