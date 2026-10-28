-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:11:19.826002+00:00
-- url     : https://prove2.me/submissions/c37b0f28-7815-47be-9c60-00529a480ea3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_above_of_finite

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  obtain ⟨M, hM, hLM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_above_of_finite
      (P := HasPlanarDrawingOn) L hL
  refine ⟨M, hLM, hM, ?_⟩
  intro N hMN hN
  exact hmax N hMN hN