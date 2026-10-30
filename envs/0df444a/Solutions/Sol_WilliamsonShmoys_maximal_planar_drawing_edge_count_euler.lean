-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:18:06.389839+00:00
-- url     : https://prove2.me/submissions/acb81cad-b5d8-434b-a257-466e64f0f73f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_edge_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawing_euler_edge_bound K hV hK
  have hNoStrict : ¬ (K.edgeSet.ncard + 6 < 3 * Fintype.card V) := by
    intro hStrict
    obtain ⟨L, hKL, hLKne, hL⟩ :=
      WilliamsonShmoys.planar_drawing_strict_edge_augmentation K hV hK hStrict
    exact hLKne (hKmax L hKL hL)
  omega