-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:21:17.957531+00:00
-- url     : https://prove2.me/submissions/9cfab8e7-cb55-4b94-a4d9-fc046a683cea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_for_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension_for_edge_count
      K hK hCard
  have hEq : L = K := hMax L hKL hL
  subst L
  exact hCount