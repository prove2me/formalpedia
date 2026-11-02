-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:53:11.538789+00:00
-- url     : https://prove2.me/submissions/847ad10d-1076-463e-9c08-ab89316db791
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_completion_with_exact_edge_count__p2m_126d21f0_5b15_4e81_98d4_afc1d569f5a6_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N) (hconn : N.Connected)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  classical
  obtain ⟨K, hNK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_completion_with_exact_edge_count__p2m_126d21f0_5b15_4e81_98d4_afc1d569f5a6_a1
      N hV hN
  have hEq : K = N := hmax K hNK hK
  subst K
  simpa using hcount