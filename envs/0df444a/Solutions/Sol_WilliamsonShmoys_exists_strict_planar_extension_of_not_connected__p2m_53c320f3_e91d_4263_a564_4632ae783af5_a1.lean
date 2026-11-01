-- Prove2me | solution 1 for WilliamsonShmoys.exists_strict_planar_extension_of_not_connected__p2m_53c320f3_e91d_4263_a564_4632ae783af5_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:34.274454+00:00
-- url     : https://prove2.me/submissions/f91e2887-42f0-4eb3-a489-66ca3a6a718f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (M : SimpleGraph V),
        HasPlanarDrawingOn M →
        ¬ M.Connected →
        ∃ N : SimpleGraph V,
          M ≤ N ∧ HasPlanarDrawingOn N ∧ ¬ N ≤ M) := by
  intro h
  letI : Fintype Empty := inferInstance
  letI : LinearOrder Empty := inferInstance
  let M : SimpleGraph Empty := ⊥
  have hM : HasPlanarDrawingOn M := by
    refine ⟨(fun v : Empty => v.elim), (fun u : Empty => u.elim), ?_⟩
    constructor
    · intro x y hxy
      exact Empty.elim x
    · constructor
      · intro u
        exact Empty.elim u
      · intro u
        exact Empty.elim u
  have hdisc : ¬ M.Connected := by
    simp [M, SimpleGraph.connected_bot_iff]
  obtain ⟨N, hMN, hN, hnotNM⟩ :=
    @h Empty inferInstance inferInstance M hM hdisc
  have hNM : N ≤ M := by
    intro u v huv
    exact Empty.elim u
  exact hnotNM hNM