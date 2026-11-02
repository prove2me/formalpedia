-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:01:10.109362+00:00
-- url     : https://prove2.me/submissions/3107f9dd-c1fb-4271-ba0f-63a51832fc59

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_drawable_supergraph__p2m_80c37abd_a278_4e21_90d9_d42081afbb20_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hR : HasPlanarDrawingOn R)
    (hMax : forall S : SimpleGraph V, (forall u v, R.Adj u v -> S.Adj u v) ->
      HasPlanarDrawingOn S ->
      (letI : DecidableRel S.Adj := Classical.decRel S.Adj
       letI : DecidableRel R.Adj := Classical.decRel R.Adj
       S.edgeFinset.card <= R.edgeFinset.card)) :
    (letI : DecidableRel R.Adj := Classical.decRel R.Adj
     R.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨S, hRS, hS, hle, hcount⟩ :=
    WilliamsonShmoys.exists_triangulated_drawable_supergraph__p2m_80c37abd_a278_4e21_90d9_d42081afbb20_a2
      R hcard hR
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  letI : DecidableRel S.Adj := Classical.decRel S.Adj
  have hmax := hMax S hRS hS
  have heq : S.edgeFinset.card = R.edgeFinset.card := Nat.le_antisymm hmax hle
  rw [heq] at hcount
  exact hcount