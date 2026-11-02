-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_maximal_extension__p2m_8348399b_8cb6_45dd_ab73_26e7cc43a44d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:06:17.396815+00:00
-- url     : https://prove2.me/submissions/ab9aa85f-ea3c-47ca-8452-e3454a591a57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
      M hM hCard
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
      H hH hCard hMax
  exact ⟨H, hMH, hCount⟩