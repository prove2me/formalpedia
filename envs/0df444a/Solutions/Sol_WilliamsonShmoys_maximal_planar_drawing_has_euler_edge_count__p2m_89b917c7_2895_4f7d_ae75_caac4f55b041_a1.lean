-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:26.570685+00:00
-- url     : https://prove2.me/submissions/3d479c8e-af89-4a53-8aee-1c0408917880
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J)
    (dJ : DecidableRel J.Adj)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel J.Adj := dJ;
      J.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel J.Adj := dJ
  exact Nat.le_antisymm
    (WilliamsonShmoys.planar_edge_count_upper_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
      J hJ dJ hcard)
    (WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_ed305078_3eca_42b1_9119_6781033ea8fa_a1
      J hJ hmax dJ hcard)