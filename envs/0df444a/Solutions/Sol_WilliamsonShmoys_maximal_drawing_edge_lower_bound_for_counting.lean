-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_lower_bound_for_counting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:35:23.712816+00:00
-- url     : https://prove2.me/submissions/d406f255-19fc-4ccd-901c-7268e1d9737d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_exact_edge_count
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    3 * (Fintype.card V : Int) - 6 <= (K.edgeSet.ncard : Int) := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_exact_edge_count K hV hK
  have hLK : L <= K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  rw [hEq] at hcount
  exact le_of_eq hcount