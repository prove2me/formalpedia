-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_facial_lengths__p2m_89410822_d74b_4a7e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:18.446379+00:00
-- url     : https://prove2.me/submissions/02b8042e-7511-43ff-815c-4aca54c8560d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_lower_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
import Theorems.Thm_WilliamsonShmoys_planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2

set_option autoImplicit false

open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (length : Fin ((letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 - Fintype.card V) → ℕ),
      2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) =
        ∑ i, length i ∧
      ∀ i, 3 ≤ length i := by
  letI : DecidableRel G.Adj := dG
  have hlow := WilliamsonShmoys.planar_drawing_connected_edge_lower_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2 G dG hConn
  have hhigh := WilliamsonShmoys.planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2 G dG hG hConn hcard
  exact WilliamsonShmoys.planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
    (Fintype.card V) G.edgeFinset.card hcard hlow hhigh