-- Prove2me | solution 1 for StabGen.RKHS.reproducing_eval_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:10:40.23682+00:00
-- url     : https://prove2.me/submissions/dc8863b6-6699-4941-a9c5-30c2040a286b

import Mathlib
import Definitions.Def_FoundationsML_Stability_IsRKHSOf

set_option autoImplicit false

open FoundationsML.Stability in
theorem solution {X H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : X → X → ℝ) (Φ : X → H) (ev : H → X → ℝ)
    (hRKHS : IsRKHSOf K Φ ev) (f : H) (x : X) :
    |ev f x| ≤ ‖f‖ * Real.sqrt (K x x) := by
  rw [hRKHS.2 f x, hRKHS.1 x x, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm f (Φ x)
