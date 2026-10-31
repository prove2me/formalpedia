-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:24:19.740499+00:00
-- url     : https://prove2.me/submissions/eceb8651-0429-46db-a278-f4c13927a572

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_augmentation__p2m_f5dec54e_fcbf_4bab_a342_af462107c326_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  by_contra hnot
  have hlt : L.edgeSet.ncard < 3 * Fintype.card V - 6 := Nat.lt_of_not_ge hnot
  obtain ⟨M, hLM, hML, hM⟩ :=
    WilliamsonShmoys.maximal_planar_edge_augmentation__p2m_f5dec54e_fcbf_4bab_a342_af462107c326_a1
      L hL hCard hlt
  exact hML (hmax M hLM hM)