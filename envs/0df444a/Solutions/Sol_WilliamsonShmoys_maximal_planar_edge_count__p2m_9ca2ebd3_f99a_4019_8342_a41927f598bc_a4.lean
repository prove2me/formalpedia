-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9ca2ebd3_f99a_4019_8342_a41927f598bc_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:20:49.507193+00:00
-- url     : https://prove2.me/submissions/edd47444-ea5f-4b7a-9acf-80b936c04fe0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_completion_with_maximal_edge_count__p2m_2f6efb11_cffe_4335_a64a_833cc169dca5_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : forall (L : SimpleGraph V) [DecidableRel L.Adj],
      HasPlanarDrawingOn L ->
      K.edgeFinset ⊆ L.edgeFinset ->
      K.edgeFinset = L.edgeFinset)
    (hV : 3 <= Fintype.card V) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  rcases
    WilliamsonShmoys.planar_completion_with_maximal_edge_count__p2m_2f6efb11_cffe_4335_a64a_833cc169dca5_a2
      K hK hV with
    ⟨L, hL, dL, hdata⟩
  letI : DecidableRel L.Adj := dL
  rcases hdata with ⟨hsub, hcount⟩
  have heq : K.edgeFinset = L.edgeFinset := hmax L hL hsub
  rw [heq]
  exact hcount