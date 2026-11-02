-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_f0debea5_402c_48d1_9751_ec911f78abab_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:20:54.607998+00:00
-- url     : https://prove2.me/submissions/0338f98e-9dd8-4fee-9ec8-cb5421565ee4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, ∃ (hNdec : DecidableRel N.Adj),
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      (∀ (P : SimpleGraph V) [DecidableRel P.Adj],
        N ≤ P → HasPlanarDrawingOn P → P = N) := by
  classical
  let p : SimpleGraph V → Prop := fun G => M ≤ G ∧ HasPlanarDrawingOn G
  obtain ⟨N, hNdec, hN⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (p := p)).mpr
      ⟨M, le_rfl, hM⟩
  refine ⟨N, hNdec, hN.1.1, hN.1.2, ?_⟩
  intro P _ hNP hP
  have hP' : p P := ⟨hN.1.1.trans hNP, hP⟩
  exact ((SimpleGraph.IsExtremal.le_iff_eq hN hP').mp hNP).symm