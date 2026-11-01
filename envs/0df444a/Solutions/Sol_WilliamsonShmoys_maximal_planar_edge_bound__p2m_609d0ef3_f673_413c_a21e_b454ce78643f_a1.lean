-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_609d0ef3_f673_413c_a21e_b454ce78643f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:10.938479+00:00
-- url     : https://prove2.me/submissions/567c5309-9ebe-42f8-8f93-a5f65eda0c58
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion__p2m_03d1095c_703e_4187_9b91_3791c513ec62_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y → HasPlanarDrawingOn Y → Y = X) :
    letI : DecidableRel X.Adj := Classical.decRel X.Adj
    3 * Fintype.card V - 6 ≤ X.edgeFinset.card := by
  classical
  obtain ⟨Y, hXY, hY, htri⟩ :=
    WilliamsonShmoys.maximal_planar_completion__p2m_03d1095c_703e_4187_9b91_3791c513ec62_a2
      X hX hcard
  have hEq : Y = X := hmax Y hXY hY
  subst Y
  exact le_of_eq htri