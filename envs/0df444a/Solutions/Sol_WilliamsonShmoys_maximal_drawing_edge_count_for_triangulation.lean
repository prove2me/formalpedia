-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count_for_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:41:36.881726+00:00
-- url     : https://prove2.me/submissions/c32222fc-902b-4153-9c2c-6e66facad74d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulating_planar_supergraph_edge_count

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, J ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J) :
    3 * Fintype.card V = J.edgeSet.ncard + 6 := by
  obtain ⟨K, hJK, hK, hcount⟩ :=
    WilliamsonShmoys.exists_triangulating_planar_supergraph_edge_count J hJ hcard
  have hKJ : K ≤ J := hmax K hJK hK
  have hEq : K = J := le_antisymm hKJ hJK
  simpa [hEq] using hcount
