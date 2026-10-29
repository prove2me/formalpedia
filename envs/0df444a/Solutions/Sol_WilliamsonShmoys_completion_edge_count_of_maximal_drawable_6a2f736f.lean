-- Prove2me | solution 1 for WilliamsonShmoys.completion_edge_count_of_maximal_drawable_6a2f736f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:47:36.151648+00:00
-- url     : https://prove2.me/submissions/7f1f2b11-d682-4e35-ab86-a18f836eab3c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_completion_aad9569e3b024b25a2de035820e22467
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ¬ ∃ H : SimpleGraph V,
      K < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hHdraw, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_edge_count_completion_aad9569e3b024b25a2de035820e22467
      K hV hK
  have hnot : ¬ K < H := by
    intro hstrict
    exact hmax ⟨H, hstrict, hHdraw⟩
  have hHK : H ≤ K := by
    by_contra hHK
    have hne : K ≠ H := by
      intro heq
      exact hHK (le_of_eq heq.symm)
    exact hnot ((lt_iff_le_and_ne).2 ⟨hKH, hne⟩)
  have hEq : H = K := le_antisymm hHK hKH
  simpa [hEq] using hHcard