-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_triangulation_exact_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:58:25.407426+00:00
-- url     : https://prove2.me/submissions/d6778864-ea10-4296-b0c7-32df1b3fbd99

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_57da26e6_40fa_4eeb_a0ea_166241e54306

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, N <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K <= N) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by
  let hCompletion :=
    WilliamsonShmoys.planar_completion_edge_count_57da26e6_40fa_4eeb_a0ea_166241e54306 N hV hN
  let K : SimpleGraph V := Classical.choose hCompletion
  have hProps := Classical.choose_spec hCompletion
  have hNK : N <= K := hProps.1
  have hK : WilliamsonShmoys.HasPlanarDrawingOn K := hProps.2.1
  have hKcard : K.edgeSet.ncard = 3 * Fintype.card V - 6 := hProps.2.2
  have hKN : K <= N := hmax K hNK hK
  have hEq : N = K := le_antisymm hNK hKN
  rw [hEq]
  exact hKcard.symm