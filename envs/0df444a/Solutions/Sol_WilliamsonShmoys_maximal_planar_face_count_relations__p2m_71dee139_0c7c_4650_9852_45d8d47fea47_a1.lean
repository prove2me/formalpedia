-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_relations__p2m_71dee139_0c7c_4650_9852_45d8d47fea47_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:19:49.303769+00:00
-- url     : https://prove2.me/submissions/4b017a8e-bc00-454b-85f0-1b2533d0841d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    ∃ f : ℕ, 3 * f = 2 * N.edgeFinset.card ∧
      Fintype.card V + f = N.edgeFinset.card + 2 := by
  have hupper :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
      N hN hcard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_8584d232_b8ae_4ac2_a58e_af76bb6d7665_a3
      N hN hcard hmax
  let n := Fintype.card V
  let E := N.edgeFinset.card
  have hE : E + 6 = 3 * n := by omega
  refine ⟨2 * n - 4, ?_, ?_⟩ <;> dsimp [n, E] at * <;> omega