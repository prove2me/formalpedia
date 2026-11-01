-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_drawable_extension__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:47.167177+00:00
-- url     : https://prove2.me/submissions/80714d71-4123-416c-bbc4-18b7e3039d12

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_d413d348_2334_48d2_b3af_5d95f492f00f_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ (K : SimpleGraph V) (_hKdec : DecidableRel K.Adj),
      M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  apply WilliamsonShmoys.finite_maximal_extension__p2m_d413d348_2334_48d2_b3af_5d95f492f00f_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) (hdown := ?_) M hM
  intro G H hGH hH
  rcases hH with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedge u v huv (hGH hadj)
  · intro u v x y huv hxy hadjuv hadjxy hne t ht s hs heq
    exact hcross u v x y huv hxy (hGH hadjuv) (hGH hadjxy) hne t ht s hs heq