-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:05.243322+00:00
-- url     : https://prove2.me/submissions/113cd1c4-c9e6-41eb-b138-4a0a4b9be989

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by
  classical
  let S : Set (SimpleGraph V) :=
    {N | M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N}
  have hSF : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hN, hmax⟩ := hSF.exists_maximal hSne
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro P hNP hP
  have hPmem : P ∈ S := ⟨le_trans hN.1 hNP, hP⟩
  have hPN : P ≤ N := hmax hPmem hNP
  exact le_antisymm hPN hNP