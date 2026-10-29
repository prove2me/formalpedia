-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation__p2m_bc657f31_eaae_4f57_ab42_14b02319f13d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:33:55.062737+00:00
-- url     : https://prove2.me/submissions/d6c6e80e-e75f-42d2-986a-3cf4b0713315
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hlt : U.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W ∧ U < W := by
  obtain ⟨W, hW, hUW, hWmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1 U hU
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
      W hW hCard hWmax
  have hne : U ≠ W := by
    intro heq
    subst W
    omega
  refine ⟨W, hW, ?_⟩
  change U ≤ W ∧ ¬ W ≤ U
  exact ⟨hUW, fun hWU => hne (le_antisymm hUW hWU)⟩