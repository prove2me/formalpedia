-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_has_maximal_extension__p2m_c3b679a7_5abb_4fff_8dba_61888269c901_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:51:37.605786+00:00
-- url     : https://prove2.me/submissions/7e31ab52-7f22-47c3-8e05-299e46e088ab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨L, le_rfl, hL⟩
  obtain ⟨H, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  have hHmem : H ∈ S := hHmax.1
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro K hHK hK
  have hKmem : K ∈ S := ⟨hHmem.1.trans hHK, hK⟩
  exact (hHmax.eq_of_le hKmem hHK).symm