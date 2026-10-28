-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_cardinality_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:14:34.766333+00:00
-- url     : https://prove2.me/submissions/713cc558-9c1d-4f5c-8d17-c6c330dbd928
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_extension_f663d05c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      ∀ ⦃u v⦄, L.Adj u v → K.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hcard⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_extension_f663d05c K hK hV
  have hEq : L = K := by
    ext u v
    constructor
    · exact @hmax L hKL hL u v
    · exact @hKL u v
  simpa [hEq] using hcard.le