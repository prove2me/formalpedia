-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:48.911449+00:00
-- url     : https://prove2.me/submissions/02962977-ec90-45d8-ab89-a18dd942228b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d5e355eb_db93_4745_85ca_eb9a9a9b0ce3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDraw, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_d5e355eb_db93_4745_85ca_eb9a9a9b0ce3_a1
      K hDraw hCard
  have hEq : L = K := hMax L hKL hLDraw
  rw [← hEq]
  exact hCount