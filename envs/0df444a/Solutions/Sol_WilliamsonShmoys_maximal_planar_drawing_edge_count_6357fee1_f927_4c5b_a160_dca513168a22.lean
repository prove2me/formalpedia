-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_6357fee1_f927_4c5b_a160_dca513168a22
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:35:23.358264+00:00
-- url     : https://prove2.me/submissions/ef49c5f1-b175-44f9-bf44-49a82e737743

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_triangulation_extension_baad2582_408f_4cf5_91c1_4db79dadb6d2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_euler_triangulation_extension_baad2582_408f_4cf5_91c1_4db79dadb6d2
      K hV hK
  have hLK : L <= K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  exact hcount