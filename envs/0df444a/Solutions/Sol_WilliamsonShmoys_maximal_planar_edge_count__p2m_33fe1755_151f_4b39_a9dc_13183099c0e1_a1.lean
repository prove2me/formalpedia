-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:55.599366+00:00
-- url     : https://prove2.me/submissions/c5566946-7cbc-4b41-a95c-f4154828aba5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
import Theorems.Thm_WilliamsonShmoys_maximality_edge_lower_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (dM : DecidableRel M.Adj),
      (letI : DecidableRel M.Adj := dM;
        M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  let dM : DecidableRel M.Adj := Classical.decRel _
  letI : DecidableRel M.Adj := dM
  have hupper :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
      M dM hM hcard
  have hlower :=
    WilliamsonShmoys.maximality_edge_lower_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
      M dM hM hmax hcard
  exact ⟨dM, by omega⟩