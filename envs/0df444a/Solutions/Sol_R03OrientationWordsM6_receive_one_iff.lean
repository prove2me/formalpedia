-- Prove2me | solution 1 for R03OrientationWordsM6.receive_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:34:50.64251+00:00
-- url     : https://prove2.me/submissions/404f63d7-a00e-497e-a8a9-b134f00eb3c9

import Mathlib.Data.Fintype.Pi
import Definitions.Def_r03_defs_67e8a31036_m6_OrientationWords

/- Candidate-only orientation-word algebra, NOT a graph or root theorem.
A nontrivial alternating component has k+1 virtual matching edges. A bit
chooses which adjacent ordinary edge receives its old center. Each ordinary
edge must receive exactly one center. k=0 includes a labelled parallel pair,
whose physical lift is a triangle. Common matching edges are not components.
The translation from graphs to this encoding requires separate review. -/
namespace R03OrientationWordsM6

end R03OrientationWordsM6

open R03OrientationWordsM6
theorem solution (a b : Bool) : receive a b = 1 ↔ a = b := by
  cases a <;> cases b <;> decide
