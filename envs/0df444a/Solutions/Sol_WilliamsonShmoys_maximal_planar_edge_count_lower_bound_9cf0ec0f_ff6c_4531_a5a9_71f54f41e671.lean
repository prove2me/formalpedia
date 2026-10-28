-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:29:44.867635+00:00
-- url     : https://prove2.me/submissions/25ae07f9-d7e6-41af-bc06-6a79373a21e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
import Theorems.Thm_WilliamsonShmoys_edge_ncard_mono_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * (Fintype.card V : Int) - 6 ≤ (K.edgeSet.ncard : Int) := by
  obtain ⟨L, hKL, hLplanar, hLbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
      K hK hCard
  have hLK : L ≤ K := hmax L hKL hLplanar
  exact le_trans hLbound
    (WilliamsonShmoys.edge_ncard_mono_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671 L K hLK)