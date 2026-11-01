-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_face_inequality__p2m_4d791eca_86d6_477c_bca9_50e3b58ef00f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:27:13.133477+00:00
-- url     : https://prove2.me/submissions/98719cf0-6b9b-49f8-ad6b-c718a5b7cd66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_formula__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_bound__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconn : G.Connected)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 ∧
        3 * f ≤ 2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) := by
  letI : DecidableRel G.Adj := dG
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planarDrawing_euler_formula__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
      G dG hconn hG
  have hbound :=
    WilliamsonShmoys.planarDrawing_edge_bound__p2m_7e15a8d6_7041_4a6f_b660_410e45ab60c6_a1
      G dG hG hcard
  refine ⟨f, heuler, ?_⟩
  omega