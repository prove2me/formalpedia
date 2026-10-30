-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:39:05.916832+00:00
-- url     : https://prove2.me/submissions/198a68bc-bb4e-4abb-89cb-4ec8ce46f7f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b6f134b1_1184_47d3_9b56_9050192c540e_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 <= Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U →
      WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hDU, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_b6f134b1_1184_47d3_9b56_9050192c540e_a2
      T hDraw hCard
  have hUT : U ≤ T := hmax U hTU hDU
  have hEq : T = U := le_antisymm hTU hUT
  simpa [hEq] using hcount