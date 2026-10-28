-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_f663d05c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:58:10.57829+00:00
-- url     : https://prove2.me/submissions/1a7081be-15f2-44fe-915b-dc8210590aa5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v⦄, L.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨K, hLK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_exact_edge_count L hL hV
  have hEq : K = L := hmax K hLK hK
  rw [hEq] at hcount
  omega