-- Prove2me | solution 1 for PersistClust.Count.qse_member_demands_high_far
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-13T16:28:47.659774+00:00
-- url     : https://prove2.me/submissions/852d140a-fc30-4c5a-8b34-8e7bccb6873d

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

theorem solution {D : EReal × EReal → ℕ∞} {α ε : ℝ}
    (a : {x : offD D // DemandsOff α ε x}) (hmem : offPt a.1 ∈ QSE α) :
    offPt a.1 ∈ QSE α ∧ α + ε < (offPt a.1).1 ∧
      2 * ε < (offPt a.1).1 - (offPt a.1).2 := by
  rcases a.2 with hp | hq
  · exact absurd hp.1.2 (not_lt.mpr hmem.2)
  · exact hq
