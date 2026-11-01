-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_f2cfae8b_743a_4350_8c03_fa33aa7b455e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:06:26.09046+00:00
-- url     : https://prove2.me/submissions/8c170092-9e69-4951-95f2-537a148a2d7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_has_triangulated_counts__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
import Theorems.Thm_WilliamsonShmoys_triangulated_counts_lower_bound__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      3 * Fintype.card V - 6 ≤ K.edgeFinset.card) := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨f, hEuler, htri⟩ :=
    WilliamsonShmoys.maximal_drawing_has_triangulated_counts__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
      K hK hmax hcard
  exact WilliamsonShmoys.triangulated_counts_lower_bound__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
    (Fintype.card V) K.edgeFinset.card hcard f hEuler htri