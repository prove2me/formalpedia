-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_d413d348_2334_48d2_b3af_5d95f492f00f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:01.964384+00:00
-- url     : https://prove2.me/submissions/ff4cbdd9-74b1-4f1c-b517-1e7fbd2ad4d7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : P M) :
    ∃ (K : SimpleGraph V) (_hKdec : DecidableRel K.Adj),
      M ≤ K ∧ P K ∧
      ∀ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
        K ≤ L → P L → L ≤ K := by
  classical
  obtain ⟨K, hMK, hKmax⟩ := Finite.exists_le_maximal (p := P) hM
  refine ⟨K, inferInstance, hMK, hKmax.1, ?_⟩
  intro L _hLdec hKL hL
  exact hKmax.2 hL hKL