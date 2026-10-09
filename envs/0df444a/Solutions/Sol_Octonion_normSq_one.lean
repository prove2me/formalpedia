-- Prove2me | solution 1 for Octonion.normSq_one
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:32:31.364238+00:00
-- url     : https://prove2.me/submissions/df02b18f-4648-435f-92e9-9679406919d1

import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace Octonion

end Octonion

open Octonion

/-- The norm of one is one. -/
@[simp]
theorem solution : Octonion.normSq (1 : octonions ℚ) = 1 := by simp [Octonion.normSq]

namespace Octonion


end Octonion
