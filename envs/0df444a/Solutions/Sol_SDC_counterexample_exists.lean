-- Prove2me | solution 1 for SDC.counterexample_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:57:54.987992+00:00
-- url     : https://prove2.me/submissions/612b4a21-9ff2-4865-82c6-d9544f7c340a

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density
import Theorems.Thm_OAI_SidorenkoCounterexample_main

theorem solution :
    ∃ size : ℕ, 0 < size ∧ ∃ host : SimpleGraph (Fin size),
      (∃ left right, host.Adj left right) ∧
      SDC.homDensity SDC.H host < (SDC.edgeDensity host) ^ 66 := by
  obtain ⟨size, hs, host, hadj, hlt⟩ := OAI.SidorenkoCounterexample.main
  have hH : SDC.H = OAI.SidorenkoCounterexample.H := by
    ext a b
    cases a <;> cases b <;> exact Iff.rfl
  refine ⟨size, hs, host, hadj, ?_⟩
  rw [hH]
  exact hlt
