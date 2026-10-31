-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_d11b870bf6364341
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:59:41.29944+00:00
-- url     : https://prove2.me/submissions/08450eee-3662-480e-8b5d-986fc2d05642

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
import Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_below_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N <= P → HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c N hN hCard
  have hNotSmall : ¬ N.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    intro hSmall
    obtain ⟨P, hSub, hNe, hPlanar⟩ :=
      WilliamsonShmoys.planar_drawing_strict_extension_below_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
        N hN hCard hSmall
    exact hNe (hmax P hSub hPlanar)
  omega