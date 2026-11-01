-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:14:32.599517+00:00
-- url     : https://prove2.me/submissions/63e1245e-a146-4c0a-9b24-1dc846ead288

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V,
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let s : Set (SimpleGraph V) :=
    {H | G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H}
  have hs : s.Nonempty := ⟨G, le_rfl, hG⟩
  have hfin : s.Finite := Set.Finite.subset Set.finite_univ (by
    intro H hH
    simp)
  obtain ⟨H, hHmax⟩ := hfin.exists_maximal hs
  have hHmem : H ∈ s := hHmax.1
  have hHmax' : ∀ K, K ∈ s → H ≤ K → K ≤ H := hHmax.2
  rcases hHmem with ⟨hGH, hHplanar⟩
  refine ⟨H, hGH, hHplanar, ?_⟩
  intro K hHK hKplanar
  have hKH : K ≤ H := hHmax' K ⟨hGH.trans hHK, hKplanar⟩ hHK
  exact (le_antisymm hHK hKH).symm