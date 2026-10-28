-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_ef555edc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:12:14.501992+00:00
-- url     : https://prove2.me/submissions/71e2d1fe-adc6-40d3-9a31-9d0e52dc57dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_augmentation

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  classical
  obtain ⟨L, hsub, hL, hbound⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_augmentation K hV hK
  have hEq : K.edgeSet = L.edgeSet := by
    apply Set.Subset.antisymm hsub
    intro e he
    by_contra hnot
    have hproper : K.edgeSet ⊂ L.edgeSet :=
      Set.ssubset_iff_subset_ne.mpr ⟨hsub, by
        intro heq
        apply hnot
        rw [heq]
        exact he⟩
    exact hmax L hproper hL
  simpa [hEq] using hbound