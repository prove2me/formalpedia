-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_max_ncard__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:15.255526+00:00
-- url     : https://prove2.me/submissions/473e8cb5-b097-4cd7-995e-e08e14f01eb7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        K ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  let S : Set ℕ :=
    {n | ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard = n}
  have hSfin : S.Finite := by
    apply (Set.finite_Iic (Nat.card (Sym2 V))).subset
    intro n hn
    rcases hn with ⟨L, hKL, hDraw, hEq⟩
    rw [← hEq]
    exact Set.mem_Iic.mpr (Set.ncard_le_card L.edgeSet)
  have hSne : S.Nonempty := by
    refine ⟨K.edgeSet.ncard, ?_⟩
    exact ⟨K, le_rfl, hK, rfl⟩
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image S id hSfin hSne
  rcases hn with ⟨L, hKL, hDraw, hEq⟩
  refine ⟨L, hKL, hDraw, ?_⟩
  intro M hKM hDrawM
  have hM : M.edgeSet.ncard ∈ S := ⟨M, hKM, hDrawM, rfl⟩
  have hbound : M.edgeSet.ncard ≤ n := hmax (M.edgeSet.ncard) hM
  rw [hEq]
  exact hbound