-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_6b45552a_e614_43a1_bcb2_5a02dc98d5fe_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:39:38.58311+00:00
-- url     : https://prove2.me/submissions/1c2c3dd5-64e0-4de5-8e0e-b121445a98ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_543fa1c4_4e11_411c_bac5_e006f931bb82_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ H' : SimpleGraph V, H ≤ H' → H' ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn H')
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨H', hle, hDraw', hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension__p2m_543fa1c4_4e11_411c_bac5_e006f931bb82_a2 H hDraw hV
  have hEq : H' = H := by
    by_contra hne
    exact hMax H' hle hne hDraw'
  subst H'
  exact hcount.le