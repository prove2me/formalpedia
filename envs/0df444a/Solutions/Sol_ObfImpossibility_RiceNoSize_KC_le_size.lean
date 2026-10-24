-- Prove2me | solution 1 for ObfImpossibility.RiceNoSize.KC_le_size
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T22:33:03.788879+00:00
-- url     : https://prove2.me/submissions/2dd08b82-bac5-4973-a8bc-52593654455a

import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

open ObfImpossibility.RiceNoSize

theorem solution (M : Machine) : KC (fn M) ≤ size M := by
  exact Nat.sInf_le ⟨M, rfl, rfl⟩
