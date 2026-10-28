-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_7842deb4_e63b_4553_baf8_30586367a025
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:37:05.145039+00:00
-- url     : https://prove2.me/submissions/2748bf8e-1e3b-4547-b29b-b07917b35242
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_drawable_supergraph_for_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V)
    (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ T : SimpleGraph V, S ≤ T →
      WilliamsonShmoys.HasPlanarDrawingOn T → T ≤ S) :
    3 * Fintype.card V = S.edgeSet.ncard + 6 := by
  obtain ⟨T, hST, hTdraw, hTcount⟩ :=
    WilliamsonShmoys.exists_triangulated_drawable_supergraph_for_edge_count
      S hSdraw hCard
  have hTS : T ≤ S := hMax T hST hTdraw
  have hEq : S = T := le_antisymm hST hTS
  simpa [hEq] using hTcount