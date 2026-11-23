-- Prove2me | solution 1 for OracleStateHSP.eq_57
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:18:25.193797+00:00
-- url     : https://prove2.me/submissions/84dcca15-f72c-461b-a97e-f801d201369e

import Mathlib
import Definitions.Def_OracleStateHSP_fracOracle

open OracleStateHSP

theorem solution (r m : ℕ) (f : V m → V m) :
    fracOracle 1 r f = Matrix.kronecker !![0, -1; 1, 0] (paddedOracle r f) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  fin_cases a <;> fin_cases b <;>
    simp [fracOracle, Matrix.kroneckerMap_apply]
