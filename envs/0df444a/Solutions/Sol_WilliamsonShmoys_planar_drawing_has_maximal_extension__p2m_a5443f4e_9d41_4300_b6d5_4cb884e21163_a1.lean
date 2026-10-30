-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_a5443f4e_9d41_4300_b6d5_4cb884e21163_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:56.636747+00:00
-- url     : https://prove2.me/submissions/4542296c-0e8e-48ec-b691-e5a1bacce6d1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | J ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hfinite : S.Finite := Set.toFinite S
  have hnonempty : S.Nonempty := ⟨J, le_rfl, hDraw⟩
  obtain ⟨K, hKmax⟩ := hfinite.exists_maximal hnonempty
  refine ⟨K, hKmax.1.1, hKmax.1.2, ?_⟩
  intro L hKL hLDraw
  have hLmem : L ∈ S := ⟨le_trans hKmax.1.1 hKL, hLDraw⟩
  have hLK : L ≤ K := hKmax.2 hLmem hKL
  exact le_antisymm hLK hKL