-- Prove2me | solution 1 for StableMatching.example3_stable_iff
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T15:10:49.994005+00:00
-- url     : https://prove2.me/submissions/bbbd979a-f940-4aae-98b8-e1a03417d51b

import Mathlib
import Definitions.Def_StableMatching_GaleShapley

set_option autoImplicit false

open StableMatching

namespace StableMatching.GSEx

set_option maxRecDepth 100000 in
/-- Exhaustive check over all `3! = 6` matchings of the Wikipedia example: exactly the
matchings `A–Y, B–Z, C–X`, `A–X, B–Y, C–Z` and `A–Z, B–X, C–Y` are stable. -/
theorem example3_stable_iff_all : ∀ μ : Matching 3,
    (example3.IsStable μ ↔
      (⇑μ = ![1, 2, 0] ∨ ⇑μ = ![0, 1, 2] ∨ ⇑μ = ![2, 0, 1])) := by
  decide

end StableMatching.GSEx

open StableMatching.GSEx in
theorem solution (μ : Matching 3) :
    example3.IsStable μ ↔
      (⇑μ = ![1, 2, 0] ∨ ⇑μ = ![0, 1, 2] ∨ ⇑μ = ![2, 0, 1]) :=
  example3_stable_iff_all μ
