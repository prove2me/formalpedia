-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:33.28428+00:00
-- url     : https://prove2.me/submissions/eb711bd3-bbf2-4f65-a798-8d6ea35ad59c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_a5768c2e_2608_4566_9f99_2d604f38d755_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> N <= K -> K = N)
    (hcard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by
  have hExt :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_a5768c2e_2608_4566_9f99_2d604f38d755_a2
      N hplanar hcard
  cases hExt with
  | intro K hK =>
    cases hK with
    | intro hKplanar hK =>
      cases hK with
      | intro hNK hKcount =>
        have hKN : K = N := hmax K hKplanar hNK
        subst K
        omega