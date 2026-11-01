-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:32.814557+00:00
-- url     : https://prove2.me/submissions/caf4742f-91ab-44a3-b103-780c7020f9ab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨K, hKmem, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨K, hKmem.1, hKmem.2, ?_⟩
  intro L hKL hL
  have hLmem : L ∈ S := ⟨le_trans hKmem.1 hKL, hL⟩
  exact hKmax hLmem hKL