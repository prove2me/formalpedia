-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:15.418288+00:00
-- url     : https://prove2.me/submissions/d0dfb992-9ba5-440d-ad8e-42f42004755b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_e9ff0367_589f_4559_ab47_9b29f52daba8_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset ⊆ L.edgeFinset) :
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by
  classical
  obtain ⟨M, dM, hM, hsub, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_e9ff0367_589f_4559_ab47_9b29f52daba8_a1
      L dL hL hcard
  have hback : M.edgeFinset ⊆ L.edgeFinset := hmax M dM hM hsub
  have hbound : 3 * Fintype.card V - 6 <= M.edgeFinset.card := by
    rw [hcount]
  exact le_trans hbound (Finset.card_le_card hback)
