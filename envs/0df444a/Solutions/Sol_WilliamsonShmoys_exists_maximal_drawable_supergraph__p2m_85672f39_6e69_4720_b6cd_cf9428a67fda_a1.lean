-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_85672f39_6e69_4720_b6cd_cf9428a67fda_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:08.194999+00:00
-- url     : https://prove2.me/submissions/ce59240e-fc95-4da1-93a7-eb8bfad7b5d1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  classical
  let candidates : Set (SimpleGraph V) :=
    {K | H ≤ K ∧ HasPlanarDrawingOn K}
  have hHmem : H ∈ candidates := ⟨le_rfl, hH⟩
  obtain ⟨K, hHK, hKmax⟩ := candidates.toFinite.exists_le_maximal hHmem
  have hKdraw : HasPlanarDrawingOn K := hKmax.1.2
  refine ⟨K, hHK, hKdraw, ?_⟩
  intro L hKL hLdraw
  have hLmem : L ∈ candidates := ⟨le_trans hHK hKL, hLdraw⟩
  exact le_antisymm (hKmax.2 hLmem hKL) hKL
