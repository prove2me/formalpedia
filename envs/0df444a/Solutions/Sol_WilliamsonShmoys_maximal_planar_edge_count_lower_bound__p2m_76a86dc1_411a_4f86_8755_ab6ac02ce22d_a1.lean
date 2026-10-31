-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:39.904172+00:00
-- url     : https://prove2.me/submissions/b4cc9540-5248-473a-bfb9-468362ae7ef9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_of_maximal__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V - 6 ≤ T.edgeSet.ncard := by
  obtain ⟨U, hTU, hU, hUmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1
      T hV hT
  have hUT : U = T := hmax U hTU hU
  rw [← hUT]
  exact WilliamsonShmoys.maximal_planar_edge_count_of_maximal__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1
    U hV hU hUmax