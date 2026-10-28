-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_lower_bound_for_maximal_exact_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:01:08.042794+00:00
-- url     : https://prove2.me/submissions/d80410b3-1b61-4fbf-8a64-05a9e5cbc45f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_lower_bound

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hmax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    3 * Fintype.card V <= J.edgeSet.ncard + 6 := by
  obtain ⟨K, hJK, hK, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_lower_bound J hV hJ
  have hKJ : K = J := hmax K hJK hK
  simpa [hKJ] using hbound