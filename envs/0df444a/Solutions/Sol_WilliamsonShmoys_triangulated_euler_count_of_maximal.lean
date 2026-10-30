-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_euler_count_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:44:10.978043+00:00
-- url     : https://prove2.me/submissions/f36fc88e-993e-4522-95c3-f3137fc1d04f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_euler_count_def6ae5e_bde9_4d7e_98ba_cdd8403c7813

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    exists f : Nat,
      Fintype.card V + f = K.edgeSet.ncard + 2 /\
      3 * f = 2 * K.edgeSet.ncard := by
  have hEdges := WilliamsonShmoys.maximal_drawable_edge_count_for_euler_count_def6ae5e_bde9_4d7e_98ba_cdd8403c7813 K hK hCard hMax
  refine Exists.intro (2 * Fintype.card V - 4) (by constructor <;> omega)