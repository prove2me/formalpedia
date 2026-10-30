-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_f7f91e8c_5069_473d_a1c5_2fecc5af85f8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:18.264854+00:00
-- url     : https://prove2.me/submissions/43c669e0-a49d-4704-8f0d-f2651bcf2d18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_caacfef8_9dba_490e_9e07_b3138fa16d65_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := dM;
      M.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel M.Adj := dM
  classical
  obtain ⟨H, hsub, _hHplanar, hHcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_caacfef8_9dba_490e_9e07_b3138fa16d65_a1
      M hM hcard
  have hle : M.edgeFinset.card ≤ H.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)
  exact hle.trans (le_of_eq hHcard)