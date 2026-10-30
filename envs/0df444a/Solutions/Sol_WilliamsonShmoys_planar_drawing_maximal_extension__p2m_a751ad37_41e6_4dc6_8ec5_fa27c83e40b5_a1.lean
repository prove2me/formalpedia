-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:01.671462+00:00
-- url     : https://prove2.me/submissions/c8081008-0208-483d-ab06-73bc932c8590

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ K : SimpleGraph V,
        G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ G := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨H, le_rfl, hH⟩
  obtain ⟨G, hG, hGmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨G, hG.1, hG.2, ?_⟩
  intro K hGK hK
  exact hGmax ⟨le_trans hG.1 hGK, hK⟩ hGK