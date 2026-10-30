-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_maximal_planar__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:52:36.893072+00:00
-- url     : https://prove2.me/submissions/42bc1442-f4ee-46f6-ae52-6ba04b257524
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count__p2m_8fdb4f78_7a22_4d46_bd0b_609fa5b74b25_a1
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_augmentation_edge_count__p2m_8fdb4f78_7a22_4d46_bd0b_609fa5b74b25_a1 H hH hV
  have hEq : K = H := hMax K hHK hK
  simpa [hEq] using hCount