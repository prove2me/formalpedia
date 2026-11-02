-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph_closed__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:49:51.92636+00:00
-- url     : https://prove2.me/submissions/3636171b-d24b-4768-9d68-0b38c93c5597

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by
  rcases hH with ⟨p, arc, hp, hedge, hcross⟩
  refine ⟨p, arc, hp, ?_, ?_⟩
  · intro u v huv hadj
    exact hedge u v huv (hGH hadj)
  · intro u v x y huv hxy hadjG hadjG' hne t ht s hs heq
    exact hcross u v x y huv hxy (hGH hadjG) (hGH hadjG') hne t ht s hs heq