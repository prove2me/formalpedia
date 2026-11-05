-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:21:00.944102+00:00
-- url     : https://prove2.me/submissions/a5a44830-6274-4c62-8d9d-724148d7dba1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) := by
  classical
  let p : SimpleGraph V → Prop :=
    fun H => N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  have hpN : p N := ⟨le_rfl, hN⟩
  obtain ⟨H, _hNH, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := N) hpN)
  rcases hmax with ⟨hpH, hmax'⟩
  have hsub : N.edgeSet ⊆ H.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hpH.1
  have hfin : H.edgeSet.Finite := Set.toFinite _
  refine ⟨H, hpH.1, hpH.2, Set.ncard_le_ncard hsub hfin, ?_⟩
  intro K hHK hK
  exact hmax' ⟨hpH.1.trans hHK, hK⟩ hHK
