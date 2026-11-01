-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_exists__p2m_89b917c7_2895_4f7d_ae75_caac4f55b041_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:01:22.047759+00:00
-- url     : https://prove2.me/submissions/e369857a-5b3a-4d70-98d9-50960d49c0f9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V,
      G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
        ∀ K : SimpleGraph V,
          J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J := by
  classical
  let s : Set (SimpleGraph V) := {J | G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨J, hJ⟩ := hsfin.exists_maximal hsne
  refine ⟨J, hJ.1.1, hJ.1.2, ?_⟩
  intro K hJK hK
  exact hJ.2 ⟨hJ.1.1.trans hJK, hK⟩ hJK