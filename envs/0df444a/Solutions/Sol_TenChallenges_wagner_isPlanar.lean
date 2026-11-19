-- Prove2me | solution 1 for TenChallenges.wagner_isPlanar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-18T12:40:54.336721+00:00
-- url     : https://prove2.me/submissions/fe3a14a7-49d8-4534-a7ff-ffb8408c9df9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TenChallenges_Minor
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Theorems.Thm_TenChallenges_kuratowski_isPlanar
import Theorems.Thm_TenChallenges_minor_of_topologicalMinor

open TenChallenges in
theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsWagnerPlanar) :
    RobertsonSeymour1986.GM5.IsPlanar G :=
  kuratowski_isPlanar G (fun ⟨T⟩ => hG.1 (minor_of_topologicalMinor T))
    (fun ⟨T⟩ => hG.2 (minor_of_topologicalMinor T))
