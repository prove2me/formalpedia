-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:25:24.511474+00:00
-- url     : https://prove2.me/submissions/afb646e2-792b-4259-8afc-701f44b60e12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.Connected := by
  classical
  by_contra hconn
  obtain ⟨u, v, huv, hnotadj, L, hKL, hLdraw, hLadj⟩ :=
    WilliamsonShmoys.exists_planar_strict_edge_extension_of_disconnected_drawing__p2m_eac4b9bf_b9de_453f_87dd_f5b281d0717e_a1
      K hK hconn
  have hEq : L = K := hmax L hKL hLdraw
  subst L
  exact hnotadj hLadj