-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_dd73cac9_b90d_44a4_8977_1c0859414274
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:00:02.396216+00:00
-- url     : https://prove2.me/submissions/55532922-f50e-4af2-ab66-a51ed1734113

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  classical
  let S : Set (SimpleGraph V) := {K | H ≤ K ∧ HasPlanarDrawingOn K}
  have hS : S.Finite := Set.toFinite S
  have hHmem : H ∈ S := by
    change H ≤ H ∧ HasPlanarDrawingOn H
    exact ⟨le_rfl, hH⟩
  obtain ⟨K, hK⟩ := hS.exists_maximal ⟨H, hHmem⟩
  have hKprop : H ≤ K ∧ HasPlanarDrawingOn K := by
    simpa [S] using hK.1
  refine ⟨K, hKprop.1, hKprop.2, ?_⟩
  intro L hKL hLplanar
  have hLprop : H ≤ L ∧ HasPlanarDrawingOn L :=
    ⟨hKprop.1.trans hKL, hLplanar⟩
  have hLK : L ≤ K := hK.2 (by simpa [S] using hLprop) hKL
  exact le_antisymm hLK hKL