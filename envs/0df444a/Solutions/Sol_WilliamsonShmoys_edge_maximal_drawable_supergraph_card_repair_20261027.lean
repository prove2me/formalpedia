-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawable_supergraph_card_repair_20261027
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:46:18.257784+00:00
-- url     : https://prove2.me/submissions/20ac7c71-7d95-4be3-814c-fc01b0ed38d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_card_eq_three_n_sub_six

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (U : SimpleGraph V)
    (hWU : W ≤ U)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ H : SimpleGraph V, W ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      H.edgeSet.ncard ≤ U.edgeSet.ncard) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hUT, hT, hTcard⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_card_eq_three_n_sub_six
      U hV hU
  have hWT : W ≤ T := le_trans hWU hUT
  have hTU : T.edgeSet.ncard ≤ U.edgeSet.ncard := hmax T hWT hT
  have hUTcard : U.edgeSet.ncard ≤ T.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hUT)
  omega