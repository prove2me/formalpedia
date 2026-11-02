-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:40:11.395982+00:00
-- url     : https://prove2.me/submissions/ca33bc9d-d9fe-4b6a-a0ea-da69f0673db5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by
  classical
  let S : Set (SimpleGraph V) := {N | L ≤ N ∧ HasPlanarDrawingOn N}
  have hS : S.Nonempty := ⟨L, le_rfl, hL⟩
  obtain ⟨M, hM, hmax⟩ := (Set.toFinite S).exists_maximal hS
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hMN hN
  have hNS : N ∈ S := ⟨hM.1.trans hMN, hN⟩
  exact hmax hNS hMN