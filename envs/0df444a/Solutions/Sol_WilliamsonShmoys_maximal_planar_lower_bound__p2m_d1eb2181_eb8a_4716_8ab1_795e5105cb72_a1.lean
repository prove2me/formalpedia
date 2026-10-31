-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_lower_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:03:48.682088+00:00
-- url     : https://prove2.me/submissions/2801eeb3-5791-46a4-85a2-60e6cf567d1b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation__p2m_ff509257_2aef_46e4_8d24_c01568aee116_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V)
    (hMax : ∀ G : SimpleGraph V, HasPlanarDrawingOn G → H ≤ G → G ≤ H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  obtain ⟨T, hT, hHT, hCount⟩ :=
    WilliamsonShmoys.maximal_planar_triangulation__p2m_ff509257_2aef_46e4_8d24_c01568aee116_a1
      H hH hV
  have hTH : T ≤ H := hMax T hT hHT
  have hEq : H = T := le_antisymm hHT hTH
  rw [hEq, hCount]
  omega