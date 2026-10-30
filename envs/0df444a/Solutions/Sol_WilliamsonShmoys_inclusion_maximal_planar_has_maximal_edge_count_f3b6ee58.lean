-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_has_maximal_edge_count_f3b6ee58
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:49:31.997037+00:00
-- url     : https://prove2.me/submissions/98903392-a227-4e6f-bd3a-c355d458cd9c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_spanning_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ K' : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K' →
      K.edgeSet ⊆ K'.edgeSet →
      K'.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K', hK', hsub, hcount⟩ :=
    WilliamsonShmoys.planar_spanning_triangulation_extension K hV hK
  have hback : K'.edgeSet ⊆ K.edgeSet := hmax K' hK' hsub
  have heq : K.edgeSet = K'.edgeSet := Set.Subset.antisymm hsub hback
  rw [heq]
  exact hcount