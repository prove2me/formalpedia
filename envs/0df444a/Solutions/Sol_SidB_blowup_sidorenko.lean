-- Prove2me | solution 1 for SidB.blowup_sidorenko
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:16:02.631995+00:00
-- url     : https://prove2.me/submissions/e5724f3a-db93-467a-a3fd-eba6eb3410f4

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper
open SidB

theorem solution {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B) :
    ∃ p : ℕ, SatisfiesSidorenko (H.blowUp p) := by
  refine ⟨0, fun g => ?_⟩
  have h1 : (H.blowUp 0).edgeCount = 0 := by
    simp [Bigraph.edgeCount]
  have h2 : g.dens (H.blowUp 0) = 1 := by
    simp only [Graphon.dens, Graphon.EX]
    simpa using g.exp_one A inferInstance
  rw [h1, h2]; simp
