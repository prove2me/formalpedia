-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_to_edge_maximal__p2m_9aae8c1a_0088_4039_a6d9_b99fa0bd700a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:13:52.682304+00:00
-- url     : https://prove2.me/submissions/39586e9c-9e26-41d9-8c1c-4f67abd6c589

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V,
          N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by
  classical
  let S : Set (SimpleGraph V) :=
    {H | M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hNmax⟩ := hSfinite.exists_maximal hSnonempty
  have hN : M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N := hNmax.prop
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro K hNK hK
  have hKmem : S K := ⟨hN.1.trans hNK, hK⟩
  exact (hNmax.eq_of_le hKmem hNK).symm
