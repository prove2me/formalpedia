-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:48:41.662404+00:00
-- url     : https://prove2.me/submissions/79f8ef02-30c1-4019-921f-07794d6f0faa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  classical
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨H, ⟨le_rfl, hH⟩⟩
  obtain ⟨K, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  rcases hKmax with ⟨hKmem, hKmax⟩
  refine ⟨K, hKmem.1, hKmem.2, ?_⟩
  intro L hKL hL
  have hLmem : L ∈ S := ⟨hKmem.1.trans hKL, hL⟩
  have hLK : L ≤ K := hKmax hLmem hKL
  exact le_antisymm hLK hKL