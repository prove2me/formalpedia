-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanarOn_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:37:29.535679+00:00
-- url     : https://prove2.me/submissions/51f27480-a7dd-472c-9ca5-b8921bffcdde

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarCompletionOn_card

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N.edgeSet ⊂ P.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn P) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨P, hNP, hP, hPcard⟩ :=
    WilliamsonShmoys.planarCompletionOn_card N hV hN
  have hEq : N.edgeSet = P.edgeSet := by
    apply Set.Subset.antisymm hNP
    intro e heP
    by_contra heN
    have hstrict : N.edgeSet ⊂ P.edgeSet := ⟨hNP, by
      intro hrev
      exact heN (hrev heP)⟩
    exact (hmax P hstrict) hP
  rw [show N.edgeSet.ncard = P.edgeSet.ncard from congrArg Set.ncard hEq]
  exact hPcard