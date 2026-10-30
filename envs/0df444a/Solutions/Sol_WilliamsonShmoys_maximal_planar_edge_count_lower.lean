-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:12:31.524771+00:00
-- url     : https://prove2.me/submissions/3d5f2933-1665-49f6-bed5-66fbc35383ce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension_ws
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_density_bound_ws

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hLmax⟩ :=
    planar_drawing_finite_maximal_extension_ws K hK
  have hbound := maximal_drawing_density_bound_ws L hL hLmax hcard
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  simpa [hEq] using hbound