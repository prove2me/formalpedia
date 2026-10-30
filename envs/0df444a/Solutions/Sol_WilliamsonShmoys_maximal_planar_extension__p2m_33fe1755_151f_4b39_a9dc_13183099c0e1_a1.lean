-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:49:19.709623+00:00
-- url     : https://prove2.me/submissions/47a74b58-0936-44e7-b706-d3f01f499c27

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V,
          M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  let S : Set (SimpleGraph V) := {M | L ≤ M ∧ HasPlanarDrawingOn M}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := by
    refine ⟨L, ?_⟩
    simp [S, hL]
  obtain ⟨M, hMmax⟩ := hSfinite.exists_maximal hSnonempty
  rcases hMmax with ⟨hMmem, hMmaximal⟩
  change L ≤ M ∧ HasPlanarDrawingOn M at hMmem
  refine ⟨M, hMmem.1, hMmem.2, ?_⟩
  intro N hMN hN
  have hNmem : N ∈ S := by
    change L ≤ N ∧ HasPlanarDrawingOn N
    exact ⟨hMmem.1.trans hMN, hN⟩
  exact le_antisymm (hMmaximal hNmem hMN) hMN