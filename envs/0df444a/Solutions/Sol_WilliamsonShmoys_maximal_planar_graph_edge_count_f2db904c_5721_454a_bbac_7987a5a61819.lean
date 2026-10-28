-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_f2db904c_5721_454a_bbac_7987a5a61819
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:29:27.062366+00:00
-- url     : https://prove2.me/submissions/99fa10f4-4756-4561-8f57-5c9d2fc3fe08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hRmax : ∀ S : SimpleGraph V,
      R ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S → S = R)
    (hCard : 3 ≤ Fintype.card V) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper : R.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
      R hRdraw hCard
  have hlower : 3 * Fintype.card V ≤ R.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
      R hRdraw hRmax hCard
  omega