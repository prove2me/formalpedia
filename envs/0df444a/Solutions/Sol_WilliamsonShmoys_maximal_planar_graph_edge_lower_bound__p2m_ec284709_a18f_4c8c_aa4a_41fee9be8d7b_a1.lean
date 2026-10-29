-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:38:31.952721+00:00
-- url     : https://prove2.me/submissions/1ed8cc10-8c54-4264-af06-fab6b973ef99
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_f78503a9_5416_4ae7_a29c_25625a9bc1b3_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_f78503a9_5416_4ae7_a29c_25625a9bc1b3_a1
      K hK hCard
  have hEq : L = K := hmax L hKL hL
  subst L
  omega