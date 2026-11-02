-- Prove2me | solution 1 for WilliamsonShmoys.drawable_extension_by_joining_components__p2m_10785777_128a_4e88_8513_e417451ea141_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:08:29.736958+00:00
-- url     : https://prove2.me/submissions/ed08ffc5-309b-4966-971a-475370763fa0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ (V : Type) [Fintype V] [LinearOrder V]
        (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
        (hdisc : ¬ M.Connected),
        ∃ u v : V, ¬ M.Reachable u v ∧
          ∃ N : SimpleGraph V, M ≤ N ∧ N.Adj u v ∧
            HasPlanarDrawingOn N ∧ N ≠ M) := by
  intro h
  let M : SimpleGraph Empty := ⊥
  have hM : HasPlanarDrawingOn M := by
    refine ⟨(fun x => isEmptyElim x), (fun u v t => isEmptyElim u), ?_, ?_, ?_⟩
    · intro x
      exact isEmptyElim x
    · intro u
      exact isEmptyElim u
    · intro u
      exact isEmptyElim u
  have hdisc : ¬ M.Connected := by
    intro hc
    rcases hc.nonempty with ⟨x⟩
    exact isEmptyElim x
  obtain ⟨u, v, huv, N, hMN, hadj, hN, hneq⟩ := h Empty M hM hdisc
  exact isEmptyElim u