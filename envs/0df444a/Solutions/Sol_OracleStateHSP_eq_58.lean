-- Prove2me | solution 1 for OracleStateHSP.eq_58
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:19:45.535901+00:00
-- url     : https://prove2.me/submissions/8d961851-930a-46af-af87-3bd602c2827d

import Mathlib
import Definitions.Def_OracleStateHSP_fracOracle

open OracleStateHSP

theorem solution (ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε ≤ 1) (r m : ℕ) (f g : V m → V m) :
    fracOracle ε r f - fracOracle ε r g =
        (Real.sqrt ε : ℂ) • Matrix.kronecker !![0, -1; 1, 0] (paddedOracle r f - paddedOracle r g) ∧
    fracOracle ε r f - fracOracle ε r g =
        (Real.sqrt ε : ℂ) • (fracOracle 1 r f - fracOracle 1 r g) := by
  constructor
  · ext ⟨a, x⟩ ⟨b, y⟩
    fin_cases a <;> fin_cases b <;>
      (simp [fracOracle, Matrix.kroneckerMap_apply, mul_sub]; try ring)
  · ext ⟨a, x⟩ ⟨b, y⟩
    fin_cases a <;> fin_cases b <;>
      (simp [fracOracle, mul_sub]; try ring)
