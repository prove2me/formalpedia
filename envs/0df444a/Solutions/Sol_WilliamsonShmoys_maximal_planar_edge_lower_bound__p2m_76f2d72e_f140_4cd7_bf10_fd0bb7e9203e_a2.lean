-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:45:38.850135+00:00
-- url     : https://prove2.me/submissions/e6aff822-33e3-467a-b0b8-fb681470826e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_c996decd_a3a2_408a_aa7c_25c4f85a8988_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_c996decd_a3a2_408a_aa7c_25c4f85a8988_a1
      H hcard hH
  have hKH : K = H := hmax K hHK hK
  rw [hKH] at hcount
  exact hcount.le