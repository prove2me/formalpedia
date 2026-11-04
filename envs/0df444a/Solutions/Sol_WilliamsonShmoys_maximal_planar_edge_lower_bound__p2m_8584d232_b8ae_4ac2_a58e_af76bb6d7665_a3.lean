-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:39:10.006975+00:00
-- url     : https://prove2.me/submissions/0edd8b3e-d631-4466-ad2b-7970f1fddd42

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V ≤ N.edgeFinset.card + 6 := by
  let E := N.edgeFinset
  have hE : ∀ e, e ∈ E ↔ e ∈ N.edgeSet := by
    intro e
    exact SimpleGraph.mem_edgeFinset
  change 3 * Fintype.card V ≤ E.card + 6
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hEq : E = N.edgeFinset := by
    ext e
    rw [hE, SimpleGraph.mem_edgeFinset]
  rw [hEq]
  exact WilliamsonShmoys.planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1 N hN hcard hmax
