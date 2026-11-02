-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:35:50.738288+00:00
-- url     : https://prove2.me/submissions/fec87501-5beb-4199-be4e-b90161305667

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨N, le_rfl, hN⟩
  obtain ⟨K, hK, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  exact hKmax ⟨le_trans hK.1 hKL, hL⟩ hKL