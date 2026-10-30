-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:19.099835+00:00
-- url     : https://prove2.me/submissions/53959dad-fc42-4855-ad4f-e316b1f6ae2e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  classical
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ HasPlanarDrawingOn K}
  have hS : S.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hKmem, hKmax⟩ := S.toFinite.exists_maximal hS
  refine ⟨K, hKmem.1, hKmem.2, ?_⟩
  intro L hKL hL
  have hLmem : L ∈ S := ⟨le_trans hKmem.1 hKL, hL⟩
  have hLK : L ≤ K := hKmax hLmem hKL
  exact le_antisymm hLK hKL
