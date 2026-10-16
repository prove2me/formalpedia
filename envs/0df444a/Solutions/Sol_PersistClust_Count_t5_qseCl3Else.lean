-- Prove2me | solution 1 for PersistClust.Count.t5_qseCl3Else
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T11:59:35.628141+00:00
-- url     : https://prove2.me/submissions/093af97c-02da-4d9b-b984-50ef7c3a438b

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Demand-structure clause for the high-far QSE sector: for a copy
demanded off the diagonal (DemandsOff), if its point already
lies in the strict QSE quadrant (birth above alpha, death at or
below alpha), then in fact the demand is the high-far kind:
the point lies in QSE alpha with birth strictly above
alpha + eps and more than 2*eps above its death coordinate.
The two DemandsOff disjuncts are the prominent copies (which
sit strictly above alpha in BOTH coordinates, so their death
coordinate cannot be at or below alpha) and the high-far QSE
copies; a QSE-pointed demanded copy therefore carries the
full high-far bundle. -/
theorem solution {D : EReal × EReal → ℕ∞} {α ε : ℝ}
    (a : {x : offD D // DemandsOff α ε x}) (hmem : offPt a.1 ∈ QSE α) :
    offPt a.1 ∈ QSE α ∧ α + ε < (offPt a.1).1 ∧
      2 * ε < (offPt a.1).1 - (offPt a.1).2 := by
  rcases a.2 with hp | hq
  · exact absurd hp.1.2 (not_lt.mpr hmem.2)
  · exact hq
