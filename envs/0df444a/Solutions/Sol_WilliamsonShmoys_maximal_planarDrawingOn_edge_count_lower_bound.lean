-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planarDrawingOn_edge_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:15:15.79586+00:00
-- url     : https://prove2.me/submissions/dc03d55d-cad7-44c5-9983-912de26b9a2f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_augment_to_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊂ N.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn N) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hsub, hN, hcard⟩ :=
    WilliamsonShmoys.planarDrawingOn_augment_to_maximal_edge_count M hM hV
  have hnot_strict : ¬ M.edgeSet ⊂ N.edgeSet := by
    intro hstrict
    exact hMax N hstrict hN
  have hEq : M.edgeSet = N.edgeSet := by
    apply Set.Subset.antisymm hsub
    intro e he
    by_contra hne
    apply hnot_strict
    exact ⟨hsub, fun hback => hne (hback he)⟩
  have heqcard : M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    simpa [hEq] using hcard
  exact le_of_eq heqcard.symm