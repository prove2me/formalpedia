-- Prove2me | solution 1 for SingularCardinals.sch_of_gch
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:22:06.309006+00:00
-- url     : https://prove2.me/submissions/02f8596b-518b-4b76-9aba-4916e48c801f

import Mathlib
import Definitions.Def_JechStationary
import Definitions.Def_SingularCardinals_basic

universe u

open Cardinal

theorem solution (h : SingularCardinals.GCH.{u}) : SingularCardinals.SCH.{u} := by
  intro κ hκ _
  exact h κ hκ.aleph0_le
