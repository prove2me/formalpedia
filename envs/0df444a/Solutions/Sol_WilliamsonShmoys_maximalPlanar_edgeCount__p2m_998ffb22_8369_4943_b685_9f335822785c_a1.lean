-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanar_edgeCount__p2m_998ffb22_8369_4943_b685_9f335822785c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:49.671969+00:00
-- url     : https://prove2.me/submissions/0d34e75c-fa17-4388-841c-ee03f4e3c17e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_extension_edgeCount__p2m_7a506924_211f_41ba_877a_336e51746219_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet →
      HasPlanarDrawingOn U → U.edgeSet ⊆ T.edgeSet) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hU, hCount⟩ :=
    WilliamsonShmoys.maximalPlanar_extension_edgeCount__p2m_7a506924_211f_41ba_877a_336e51746219_a1
      T hT hV
  have hEq : U.edgeSet = T.edgeSet := Set.Subset.antisymm (hmax U hTU hU) hTU
  simpa [hEq] using hCount