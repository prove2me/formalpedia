-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:46:00.8902+00:00
-- url     : https://prove2.me/submissions/16000837-a6d5-4088-9ac0-5edded854524
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_completion__p2m_fc0abe73_fd21_4e9c_bb3c_f4df0112280b_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨K, hHK, hK, hcardK⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_completion__p2m_fc0abe73_fd21_4e9c_bb3c_f4df0112280b_a1
      H hH hcard
  have hKH : K = H := hmax K hHK hK
  subst K
  exact hcardK