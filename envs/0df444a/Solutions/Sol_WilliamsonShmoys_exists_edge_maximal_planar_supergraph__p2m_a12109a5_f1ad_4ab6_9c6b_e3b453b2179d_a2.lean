-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:21:36.606257+00:00
-- url     : https://prove2.me/submissions/af83278c-c718-4b48-a712-211e5b2a052d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_element_finite__p2m_8824e35c_b427_4577_adf2_2966f46879ec_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N := by
  let p : SimpleGraph V → Prop := fun N => M ≤ N ∧ HasPlanarDrawingOn N
  have hne : ∃ N, p N := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hN, hmax⟩ :=
    exists_maximal_element_finite__p2m_8824e35c_b427_4577_adf2_2966f46879ec_a1 p hne
  refine ⟨N, hN.1, hN.2, ?_⟩
  intro P hNP hP
  exact hmax P ⟨le_trans hN.1 hNP, hP⟩ hNP