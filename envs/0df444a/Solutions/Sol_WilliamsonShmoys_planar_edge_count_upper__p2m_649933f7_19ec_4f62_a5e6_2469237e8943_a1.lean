-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_649933f7_19ec_4f62_a5e6_2469237e8943_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:32.688839+00:00
-- url     : https://prove2.me/submissions/7e440f0a-b088-49a6-99ee-2049c22c5fed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    : letI : DecidableRel M.Adj := dM
      2 * M.edgeFinset.card + 12 ≤ 6 * Fintype.card V := by
  have hDec : dM = (Classical.decRel _) := by
    funext u v
    exact Subsingleton.elim _ _
  subst dM
  classical
  obtain ⟨H, hMH, hH, hmax, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
      M hM
  have hbound :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
      H hH hmax hcard
  omega