-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_bfd9de26_18b5_4f80_88aa_03ffeafbf182_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:41.93975+00:00
-- url     : https://prove2.me/submissions/a568a32d-5199-4ad8-a40c-1622e316ba83

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ C : SimpleGraph V,
      G ≤ C ∧ WilliamsonShmoys.HasPlanarDrawingOn C ∧
      ∀ H : SimpleGraph V, C ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = C := by
  classical
  let s : Set (SimpleGraph V) := {C | G ≤ C ∧ WilliamsonShmoys.HasPlanarDrawingOn C}
  have hsfinite : s.Finite :=
    Set.Finite.subset Set.finite_univ (by
      intro C hC
      simp [s])
  have hsnonempty : s.Nonempty := ⟨G, by simp [s, hG]⟩
  obtain ⟨C, hmax⟩ := hsfinite.exists_maximal hsnonempty
  have hCmem : C ∈ s := hmax.1
  refine ⟨C, hCmem.1, hCmem.2, ?_⟩
  intro H hCH hH
  have hHmem : H ∈ s := ⟨hCmem.1.trans hCH, hH⟩
  have hHC : H ≤ C := hmax.2 hHmem hCH
  exact le_antisymm hHC hCH