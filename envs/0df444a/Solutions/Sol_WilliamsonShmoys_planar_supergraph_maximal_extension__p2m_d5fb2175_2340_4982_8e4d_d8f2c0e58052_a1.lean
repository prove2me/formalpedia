-- Prove2me | solution 1 for WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_d5fb2175_2340_4982_8e4d_d8f2c0e58052_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:26.039788+00:00
-- url     : https://prove2.me/submissions/09aeeb35-921e-4082-8dcc-84f0c8bcae9a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_downward_closed__p2m_9a3aed6d_2bec_4e6f_a443_353e67f8b6ae_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hConnected : G.Connected) (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_of_finite_downward_closed__p2m_9a3aed6d_2bec_4e6f_a443_353e67f8b6ae_a1
      (V := V) HasPlanarDrawingOn
      (by
        intro A B hAB hB
        rcases hB with ⟨p, arc, hp, hseg, hcross⟩
        refine ⟨p, arc, hp, ?_, ?_⟩
        · intro u v huv hadj
          exact hseg u v huv (hAB hadj)
        · intro u v x y huv hxy hadj hadj' hne
          exact hcross u v x y huv hxy (hAB hadj) (hAB hadj') hne)
      G hDraw
  exact ⟨H, hGH, hH, fun K hHK hK => hmax K hHK hK⟩