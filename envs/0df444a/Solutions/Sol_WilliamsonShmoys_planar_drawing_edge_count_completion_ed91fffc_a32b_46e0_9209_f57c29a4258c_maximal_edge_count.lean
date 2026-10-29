-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:08:52.890329+00:00
-- url     : https://prove2.me/submissions/0fe0ea58-b84f-485c-b5e2-6ff284fef27c

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_saturated_extension_for_maximal_edge_count_retry2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count_retry2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K <= L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L <= K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨L, hKL, hL, hSat⟩ :=
    WilliamsonShmoys.planar_drawing_edge_saturated_extension_for_maximal_edge_count_retry2
      K hV hK
  have hLK : L <= K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  exact WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_retry2
    L hV hL hSat