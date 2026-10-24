-- Prove2me | solution 1 for ObfImpossibility.RiceNoSize.Pi_closed
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T22:33:02.502995+00:00
-- url     : https://prove2.me/submissions/e2c76282-ea73-49d7-b721-a7d46a049d00

import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

open ObfImpossibility.RiceNoSize

theorem solution : ClosedUnderFn PiY PiN := by
  intro M M' h
  simp only [PiY, PiN, Set.mem_setOf_eq, AlwaysHalts, h, iff_self, and_self]
