-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:30.593714+00:00
-- url     : https://prove2.me/submissions/735fef00-0eb2-4dee-8fc8-414c16e0acec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_09a7ea27_8f3a_49eb_bec8_9d191564106c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J) :
    3 * Fintype.card V - 6 = J.edgeSet.ncard := by
  obtain ⟨K, hJK, hK, hKcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_09a7ea27_8f3a_49eb_bec8_9d191564106c_a1
      J hJ hV
  have hKJ : K ≤ J := hmax K hJK hK
  have hEq : K = J := le_antisymm hKJ hJK
  simpa [hEq] using hKcard