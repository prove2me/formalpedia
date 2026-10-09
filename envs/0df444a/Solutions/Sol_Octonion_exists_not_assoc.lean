-- Prove2me | solution 1 for Octonion.exists_not_assoc
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:29:34.342353+00:00
-- url     : https://prove2.me/submissions/963fd05b-7b1f-4b39-ab9d-74e27256efe1

import Definitions.Def_Octonion_octonions
import Definitions.Def_Octonion_toRat8
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace Octonion

end Octonion

open Octonion

/-- The octonions are not associative: `((i,0)*(j,0))*(0,1) = (0,k)` but
`(i,0)*((j,0)*(0,1)) = (0,−k)`. Checked by computation on the rational coordinates. -/
theorem solution : ∃ x y z : octonions ℚ, (x * y) * z ≠ x * (y * z) := by
  refine ⟨(⟨⟨0, 1, 0, 0⟩, 0⟩ : octonions ℚ), (⟨⟨0, 0, 1, 0⟩, 0⟩ : octonions ℚ),
    (⟨0, 1⟩ : octonions ℚ), ?_⟩
  decide +kernel

namespace Octonion


end Octonion
