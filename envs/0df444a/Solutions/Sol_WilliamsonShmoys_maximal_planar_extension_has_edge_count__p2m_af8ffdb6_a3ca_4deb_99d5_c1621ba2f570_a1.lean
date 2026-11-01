-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_has_edge_count__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:06:31.504715+00:00
-- url     : https://prove2.me/submissions/001fcac9-b53c-491c-b43c-6dd7709bc8a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
import Theorems.Thm_WilliamsonShmoys_planar_triangulating_extension_lower_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N <= M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
      3 * Fintype.card V = M.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  obtain ⟨N, hMN, hN, hLower⟩ :=
    WilliamsonShmoys.planar_triangulating_extension_lower_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
      M hM hcard
  have hNM : N <= M := hmax N hMN hN
  have hEq : N = M := le_antisymm hNM hMN
  subst N
  have hUpper :=
    WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
      M hM hcard
  exact Nat.le_antisymm hLower hUpper