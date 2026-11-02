-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_71c4bf82_58f5_4c33_a47c_7b17640d4f06_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:03:45.339075+00:00
-- url     : https://prove2.me/submissions/aae6127a-ccde-4fde-ada7-dfab6e5ecfb4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_exists_maximal_above_in_finite_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    Exists (fun N : SimpleGraph V =>
      M <= N ∧ HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V, N <= K → HasPlanarDrawingOn K → K = N) := by
  obtain ⟨N, hN, hMN, hmax⟩ :=
    exists_maximal_above_in_finite_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1
      (fun G : SimpleGraph V => M <= G ∧ HasPlanarDrawingOn G) M ⟨le_rfl, hM⟩
  refine ⟨N, hMN, hN.2, ?_⟩
  intro K hNK hK
  exact hmax K hNK ⟨hMN.trans hNK, hK⟩
