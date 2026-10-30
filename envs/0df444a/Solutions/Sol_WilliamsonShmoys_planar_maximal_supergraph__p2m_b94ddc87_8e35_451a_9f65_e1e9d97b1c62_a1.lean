-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:27:20.743021+00:00
-- url     : https://prove2.me/submissions/aa01274e-5c73-4f2b-9201-6018ca893ca9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_supergraph_of_downward_closed__p2m_1a00a7f7_bc24_43af_b949_dc9c9c992368_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  apply finite_maximal_supergraph_of_downward_closed__p2m_1a00a7f7_bc24_43af_b949_dc9c9c992368_a1
    H HasPlanarDrawingOn hH
  intro G G' hGG' hG'
  rcases hG' with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedge u v huv (hGG' hadj)
  · intro u v x y huv hxy hadj1 hadj2 hne t ht s hs heq
    exact hcross u v x y huv hxy (hGG' hadj1) (hGG' hadj2) hne t ht s hs heq