-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_15067ae2_6164_4683_8340_3852ef322251_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:22:11.361203+00:00
-- url     : https://prove2.me/submissions/6e6010bb-35dc-48f5-979e-bce9104c94f9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (N <= K)
          (∀ L : SimpleGraph V,
            WilliamsonShmoys.HasPlanarDrawingOn L → K <= L → K = L)) := by
  classical
  let p : SimpleGraph V → Prop :=
    fun K => N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hpN : p N := ⟨le_rfl, hplanar⟩
  obtain ⟨K, _hNK, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := N) hpN)
  rcases hmax with ⟨hpK, hmax'⟩
  refine ⟨K, hpK.2, hpK.1, ?_⟩
  intro L hL hKL
  have hLK : L ≤ K := hmax' ⟨hpK.1.trans hKL, hL⟩ hKL
  exact le_antisymm hKL hLK
