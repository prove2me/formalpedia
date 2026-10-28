-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026_dad7fe2d8c9e421797660577ae1aff58
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:35:52.810889+00:00
-- url     : https://prove2.me/submissions/ef156c1b-01b3-4b5e-b281-deac7a671411
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_20261026_dad7fe2d8c9e421797660577ae1aff58_triangulation_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall K' : SimpleGraph V, K <= K' ->
      WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨K', hsub, hK', hcount⟩ :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026_dad7fe2d8c9e421797660577ae1aff58_triangulation_extension
      K hK hV
  have heq : K' = K := hmax K' hsub hK'
  simpa [heq] using hcount.le