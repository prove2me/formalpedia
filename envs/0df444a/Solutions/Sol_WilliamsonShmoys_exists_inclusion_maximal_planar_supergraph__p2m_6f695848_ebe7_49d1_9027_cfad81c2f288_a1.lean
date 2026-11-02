-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_6f695848_ebe7_49d1_9027_cfad81c2f288_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:10:54.699313+00:00
-- url     : https://prove2.me/submissions/e49c3f92-aeab-4de2-bd33-7bf966b84dac

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V, N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | N ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite _
  have hSnonempty : S.Nonempty := ⟨N, le_rfl, hN⟩
  obtain ⟨P, hP, hPmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨P, hP.1, hP.2, ?_⟩
  intro Q hPQ hQ
  have hQinS : Q ∈ S := ⟨le_trans hP.1 hPQ, hQ⟩
  have hQP : Q ≤ P := hPmax hQinS hPQ
  exact (le_antisymm hPQ hQP).symm